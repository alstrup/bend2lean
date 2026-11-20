// bend2lean: translate Bend definitions, laws and proofs into Lean 4, so Lean's kernel
// re-checks them. Reads a file with Bend's own loader (bend2/bend.ts), walks every def
// the file's own defs reach (Base included), and prints one Lean file.
//
//   BEND_DIR=<bend checkout> bun bend2lean.ts <file.bend> [out.lean]
//
// Core forms: Mat chains become `fun x => match x with`, %e : P becomes
// Eq.mp (congrArg (fun x => P) e) f, {==} becomes rfl. Nat, Bool, List, pairs, Unit and
// Empty map to Lean's; quantities are erased.
import * as fs from "fs";
import * as os from "os";
import * as path from "path";

const BEND_DIR = process.env.BEND_DIR ?? path.join(import.meta.dir, "..", "bend");
const B: any = await import(path.join(BEND_DIR, "bend2", "bend.ts"));

type T = any;
const file = process.argv[2];
const out = process.argv[3];
const book = B.book_nil();
await B.book_load(book, file, "", new Map());
const low = (t: T) => B.term_lower(t, 0);

const fail = (msg: string, t?: T): never => {
  throw new Error(msg + (t ? " in " + JSON.stringify(t, (k, v) => (k === "s" ? undefined : v)).slice(0, 300) : ""));
};

// Names
const lname = (k: string) => "«" + k + "»";
const vname = (k: string, i: number) => (k === "" || k === "_" ? "x" : k.replace(/[^A-Za-z0-9_]/g, "_")) + "_" + i;

// Quantity binders are erased: per def, which parameter positions are quantities
const qpos: Record<string, boolean[]> = {};
function params(t: T): boolean[] {
  const r: boolean[] = [];
  while (t.$ === "All") { r.push(t.A.$ === "Qnt"); t = t.B; }
  return r;
}

const ADTS: Record<string, (xs: string[]) => string> = {
  Nat: () => "Nat", Bool: () => "Bool", Unit: () => "Unit", Empty: () => "Empty",
  List: (xs) => `(List ${xs[0]})`,
  "Word.Nil": () => "(BWord 0)",
  "Word.Con": (xs) => `(BWord (Nat.succ ${xs[0]}))`,
};
const CTRS: Record<string, { pat: (fs: string[]) => string; term: (fs: string[]) => string; n: number }> = {
  Zero: { n: 0, pat: () => "Nat.zero", term: () => "Nat.zero" },
  Succ: { n: 1, pat: ([p]) => `Nat.succ ${p}`, term: ([p]) => `(Nat.succ ${p})` },
  False: { n: 0, pat: () => "false", term: () => "false" },
  True: { n: 0, pat: () => "true", term: () => "true" },
  Nil: { n: 0, pat: () => "[]", term: () => "[]" },
  Con: { n: 2, pat: ([h, t]) => `${h} :: ${t}`, term: ([h, t]) => `(${h} :: ${t})` },
  Tuple: { n: 2, pat: ([a, b]) => `(${a}, ${b})`, term: ([a, b]) => `(${a}, ${b})` },
  Unit: { n: 0, pat: () => "()", term: () => "()" },
  WNil: { n: 0, pat: () => "BWord.nil", term: () => "BWord.nil" },
  WCon: { n: 2, pat: ([h, t]) => `BWord.con ${h} ${t}`, term: ([h, t]) => `(BWord.con ${h} ${t})` },
};

const used = new Set<string>();
const ren = new Map<number, string>();
const inlined = new Map<string, T>();
const inlining = new Set<string>();
const props = new Set<string>();
const user = new Set<string>();
function userCtr(k: string) {
  const c = book.ctrs[k];
  if (!c || !user.has(c.f)) return null;
  const q = `${lname(c.f)}.${lname(k)}`;
  return { n: c.n, pat: (fs: string[]) => fs.length ? `${q} ${fs.join(" ")}` : q, term: (fs: string[]) => fs.length ? `(${q} ${fs.join(" ")})` : q };
}
// a non-indexed datatype: parameters are its type's binders, fields the rest of each constructor
function inductive(k: string, d: T): string {
  let K = low(d.T);
  const ps: string[] = [];
  let np = 0;
  while (K.$ === "All") {
    np++;
    if (K.A.$ !== "Qnt") ps.push(`(${vname(K.k, K.i)} : ${K.A.$ === "Typ" ? "Type" : tm(K.A)})`);
    K = K.B;
  }
  if (K.$ !== "Typ") fail("indexed datatype " + k);
  user.add(k);
  const arms = d.c.map((c: T) => {
    let t = low(c.T);
    for (let j = 0; j < np; j++) t = t.B;
    return `  | ${lname(c.k)} : ${tm(t)}`;
  });
  return `inductive ${lname(k)} ${ps.join(" ")} : Type where\n${arms.join("\n")}\n`;
}
// levels of type variables that some List or pair holds (they must live in Type)
let dataVars = new Set<number>();
function holds(t: T, acc: Set<number>) {
  if (!t || typeof t !== "object") return;
  if (Array.isArray(t)) { t.forEach((x) => holds(x, acc)); return; }
  if (t.$ === "ADT" && (t.k === "List" || t.k === "Sigma")) {
    const walk = (x: T) => { if (x && x.$ === "Var") acc.add(x.i); else if (x && x.$ === "Lam") walk(x.f); };
    t.x.forEach(walk);
  }
  for (const k of Object.keys(t)) if (k !== "s") holds(t[k], acc);
}
let fresh = 1000;

// a type or term; Bend has one syntax for both
function tm(t: T): string {
  switch (t.$) {
    case "Var": return t.raw ? t.k : (ren.get(t.i) ?? vname(t.k, t.i));
    case "Ref": {
      if (t.k in ADTS) return ADTS[t.k]([]);
      if (t.k === "Word") return "BWord";
      if (user.has(t.k)) return lname(t.k);
      used.add(t.k);
      return lname(t.k);
    }
    case "Typ": return "Type";
    case "Lit":
      if (t.k === "Nat") return `(${t.v} : Nat)`;
      if (t.k === "U32") { used.add("U32"); return `(«U32».«U32» (bwordOf 32 ${t.v}))`; }
      return fail("literal " + t.k);
    case "All": {
      ren.delete(t.i);
      if (t.A.$ === "Qnt") return tm(t.B);
      if (t.A.$ === "Typ" && !dataVars.has(t.i)) return `((${vname(t.k, t.i)} : Sort _) → ${tm(t.B)})`;
      return `((${vname(t.k, t.i)} : ${tm(t.A)}) → ${tm(t.B)})`;
    }
    case "Lam": ren.delete(t.i); return `(fun ${vname(t.k, t.i)} => ${tm(t.f)})`;
    case "App": return app(t);
    case "ADT": {
      const xs = t.x.filter((x: T) => x.$ !== "Qua" && x.$ !== "Min").map(tm);
      if (t.k === "Sigma") {
        // Sigma<a, b, A, _ => B>: a plain pair when B ignores its argument
        const [A, Bl] = t.x.slice(2);
        if (Bl.$ !== "Lam") fail("dependent pair", t);
        return `(${tm(A)} × ${tm(Bl.f)})`;
      }
      if (t.k === "List") return ADTS.List([tm(t.x[t.x.length - 1])]);
      if (t.k in ADTS) return ADTS[t.k](xs);
      if (user.has(t.k)) return xs.length ? `(${lname(t.k)} ${xs.join(" ")})` : lname(t.k);
      return fail("datatype " + t.k, t);
    }
    case "Ctr": {
      const c = CTRS[t.k] ?? userCtr(t.k) ?? fail("constructor " + t.k, t);
      return c.term(t.x.map(tm));
    }
    case "Mat": {
      const x = "m_" + fresh++;
      return `(fun ${x} => ${mat(t, x)})`;
    }
    case "Eql": return `(@Eq ${tm(t.T)} ${tm(t.a)} ${tm(t.b)})`;
    case "Rfl": return "rfl";
    case "Rwt": {
      // %e : P; f  with P = _ => e => P'
      const p = t.p;
      if (p.$ !== "Lam" || p.f.$ !== "Lam") fail("rewrite motive", t);
      ren.delete(p.i); ren.delete(p.f.i);
      return `(Eq.mp (congrArg (fun ${vname(p.k, p.i)} => ${tm(p.f.f)}) ${tm(t.e)}) ${tm(t.f)})`;
    }
    case "Ann": return `(${tm(t.x)} : ${tm(t.T)})`;
    case "Let": {
      const parts = t.k.map((k: string, j: number) => `let ${vname(k, t.i[j])} := ${tm(t.v[j])}; `).join("");
      return `(${parts}${tm(t.f)})`;
    }
    case "Hol": return fail("open hole ?" + t.k);
    case "Efq": { const x = "e_" + fresh++; return `(fun ${x} => nomatch ${x})`; }
    default: return fail("term " + t.$, t);
  }
}

// a spine f a b ...: drop the quantity arguments of known defs; apply a Mat to its scrutinee
function app(t: T): string {
  const args: T[] = [];
  let f = t;
  while (f.$ === "App") { args.unshift(f.x); f = f.f; }
  if (f.$ === "Efq" && args.length >= 1) {
    return `(nomatch ${tm(args[0])})`;
  }
  if (f.$ === "Mat") {
    const [scr, ...rest] = args;
    const s = tm(scr);
    const body = scr.$ === "Var" ? mat(f, s) : `(fun m => ${mat(f, "m")}) ${s}`;
    return rest.length ? `((${body}) ${rest.map(tm).join(" ")})` : `(${body})`;
  }
  if (f.$ === "Ref" && inlined.has(f.k) && !inlining.has(f.k)) {
    const saved = new Map(ren);
    inlining.add(f.k);
    const s = consume(inlined.get(f.k), args.map(tm));
    inlining.delete(f.k);
    ren.clear(); for (const [a, b] of saved) ren.set(a, b);
    return `(${s})`;
  }
  if (f.$ === "Ref" && f.k === "Pair" && args.length === 2) return `(${tm(args[0])} × ${tm(args[1])})`;
  let keep = args;
  if (f.$ === "Ref" && qpos[f.k]) keep = args.filter((_, j) => !qpos[f.k][j]);
  return `(${tm(f)} ${keep.map(tm).join(" ")})`;
}

// the constructors of the type a constructor belongs to
const FAMILY: Record<string, string[]> = {
  Zero: ["Zero", "Succ"], Succ: ["Zero", "Succ"], False: ["False", "True"], True: ["False", "True"],
  Nil: ["Nil", "Con"], Con: ["Nil", "Con"], Tuple: ["Tuple"], Unit: ["Unit"], WNil: ["WNil"], WCon: ["WCon"],
};
function family(k: string): string[] {
  if (FAMILY[k]) return FAMILY[k];
  const c = book.ctrs[k];
  const d: T = c && book.tlds[c.f];
  return d && d.$ === "ADT" ? d.c.map((x: T) => x.k) : [k];
}
const ctrOf = (k: string) => CTRS[k] ?? userCtr(k) ?? fail("constructor " + k);
type Arg = string | { k: string; fs: string[] };
const argStr = (a: Arg) => (typeof a === "string" ? a : ctrOf(a.k).term(a.fs));

// a chain of λ-matches on x; each arm's handler takes the fields, then the args in rest
function mat(t: T, x: string, rest: Arg[] = []): string {
  const arms: string[] = [];
  const seen: string[] = [];
  let first = t.$ === "Mat" ? t.k : null;
  while (t.$ === "Mat") {
    const c = ctrOf(t.k);
    const fs = fieldNames(t.h, c.n);
    seen.push(t.k);
    arms.push(`| ${c.pat(fs)} => ${consume(t.h, [...fs, ...rest])}`);
    t = t.m;
  }
  if (t.$ !== "Efq") {
    // the default arm: one arm per remaining constructor, the value known to the handler
    const left = first ? family(first).filter((k) => !seen.includes(k)) : [];
    if (left.length === 0 && first) { /* every constructor is covered */ }
    else if (!first) arms.push(`| y => ${consume(t, ["y", ...rest])}`);
    for (const k of left) {
      const c = ctrOf(k);
      const fs = Array.from({ length: c.n }, () => "f_" + fresh++);
      arms.push(`| ${c.pat(fs)} => ${consume(t, [{ k, fs }, ...rest])}`);
    }
  }
  return `match ${x} with ${arms.join(" ")}`;
}

function fieldNames(h: T, n: number): string[] {
  const fs: string[] = [];
  for (let j = 0; j < n; j++) {
    if (h && h.$ === "Lam") { fs.push(vname(h.k, h.i)); h = h.f; }
    else { fs.push("f_" + fresh++); h = null; }
  }
  return fs;
}

// h applied to args: lambdas take them, λ-matches match them (or pick the arm of a known constructor)
function consume(h: T, vars: Arg[]): string {
  if (vars.length === 0) return tm(h);
  const v = vars[0];
  if (h.$ === "Lam") { ren.set(h.i, argStr(v)); return consume(h.f, vars.slice(1)); }
  if (h.$ === "Mat") {
    if (typeof v !== "string") {
      let t = h;
      while (t.$ === "Mat" && t.k !== v.k) t = t.m;
      if (t.$ === "Mat") return consume(t.h, [...v.fs, ...vars.slice(1)]);
      if (t.$ === "Efq") return fail("a known constructor reaches no arm");
      return consume(t, vars);
    }
    return `(${mat(h, v, vars.slice(1))})`;
  }
  if (h.$ === "Efq") return `(nomatch ${argStr(v)})`;
  return `(${tm(h)} ${vars.map(argStr).join(" ")})`;
}

// every def outside Base is a root: load Base alone to know its names
const baseBook = B.book_nil();
const baseFile = path.join(fs.mkdtempSync(path.join(os.tmpdir(), "bend2lean-")), "base.bend");
fs.writeFileSync(baseFile, "import Base\n");
await B.book_load(baseBook, baseFile, "", new Map());
const rootDefs = book.order.filter((k) => book.tlds[k].$ === "Def" && !(k in baseBook.tlds));
const todo = new Set<string>(rootDefs);
const emitted = new Map<string, string>();

function refs(t: T, acc: Set<string>) {
  if (!t || typeof t !== "object") return;
  if (Array.isArray(t)) { t.forEach((x) => refs(x, acc)); return; }
  if (t.$ === "Ref") acc.add(t.k);
  if (t.$ === "ADT") acc.add(t.k);
  if (t.$ === "Ctr" && book.ctrs[t.k]) acc.add(book.ctrs[t.k].f);
  for (const k of Object.keys(t)) if (k !== "s") refs(t[k], acc);
}

const need = new Set<string>();
function visit(k: string) {
  if (need.has(k) || k in ADTS || k === "Word" || k === "Pair" || k === "Sigma") return;
  const d: T = book.tlds[k];
  if (!d) return;
  need.add(k);
  const acc = new Set<string>();
  refs(low(d.T), acc);
  if (d.$ === "Def" && d.v) refs(low(d.v), acc);
  if (d.$ === "ADT") for (const c of d.c) refs(low(c.T), acc);
  for (const r of acc) visit(r);
}
for (const k of todo) visit(k);

// translate in dependency order; a def that fails, or uses one that did, is skipped
const skipped = new Map<string, string>();
const lines: string[] = ["-- generated by bend2lean from " + file, "set_option maxRecDepth 4000", "set_option linter.unusedVariables false", "namespace Bend", "",
  "-- Bend's Word(n): n bits, lowest first",
  "inductive BWord : Nat → Type where",
  "  | nil : BWord 0",
  "  | con {n : Nat} : Bool → BWord n → BWord (n + 1)",
  "",
  "-- the word Bend writes for a literal: v's bits, lowest first",
  "def bwordOf : (n : Nat) → Nat → BWord n",
  "  | 0, _ => .nil",
  "  | n + 1, v => .con (v % 2 == 1) (bwordOf n (v / 2))",
  ""];
// strongly connected components, in dependency order (Tarjan); a cycle is a mutual block
const deps = (k: string): string[] => {
  const d: T = book.tlds[k];
  const acc = new Set<string>();
  refs(low(d.T), acc);
  if (d.$ === "Def" && d.v) refs(low(d.v), acc);
  if (d.$ === "ADT") for (const c of d.c) refs(low(c.T), acc);
  return [...acc].filter((r) => need.has(r) && r !== "Word" && r !== "Pair" && r !== "Sigma");
};
const sccs: string[][] = [];
{
  let idx = 0;
  const index = new Map<string, number>(), lowl = new Map<string, number>(), on = new Set<string>(), st: string[] = [];
  const strong = (v: string) => {
    index.set(v, idx); lowl.set(v, idx); idx++; st.push(v); on.add(v);
    for (const w of deps(v)) {
      if (!index.has(w)) { strong(w); lowl.set(v, Math.min(lowl.get(v)!, lowl.get(w)!)); }
      else if (on.has(w)) lowl.set(v, Math.min(lowl.get(v)!, index.get(w)!));
    }
    if (lowl.get(v) === index.get(v)) {
      const comp: string[] = [];
      let w: string;
      do { w = st.pop()!; on.delete(w); comp.push(w); } while (w !== v);
      sccs.push(comp.reverse());
    }
  };
  for (const k of book.order) if (need.has(k) && !index.has(k) && k !== "Word" && k !== "Pair" && k !== "Sigma") strong(k);
}
// in a cycle, inline the members that do not call themselves into the others' bodies;
// the cycle then breaks into plain self-recursion (Lean unfolds that, not mutual blocks)
const selfRec = (k: string) => { const acc = new Set<string>(); const d: T = book.tlds[k]; if (d.v) refs(low(d.v), acc); return acc.has(k); };
const order: string[] = [];
const mutualOf = new Map<string, string[]>();
for (const c of sccs) {
  if (c.length === 1) { order.push(c[0]); continue; }
  let inl = c.filter((k) => book.tlds[k].$ === "Def" && !selfRec(k));
  let keep = c.filter((k) => !inl.includes(k));
  if (keep.length === 0) {
    const first = book.order.find((k) => c.includes(k))!;
    keep = [first]; inl = inl.filter((k) => k !== first);
  }
  if (inl.length && keep.length === 1) {
    for (const k of inl) inlined.set(k, low(book.tlds[k].v));
    order.push(...keep, ...inl);
  } else { for (const k of c) mutualOf.set(k, c); order.push(...c); }
}
const mutualOpen = new Set<string[]>();
for (const k of order) {
  if (emitted.has(k) || skipped.has(k)) continue;
  const mc = mutualOf.get(k);
  if (mc && !mutualOpen.has(mc)) { mutualOpen.add(mc); lines.push("mutual"); }
  const d0: T = book.tlds[k];
  if (d0.$ === "ADT") {
    if (k in ADTS) continue;
    const acc = new Set<string>();
    for (const c of d0.c) refs(low(c.T), acc);
    const bad = [...acc].find((r) => r !== k && r !== "Word" && r !== "Pair" && r !== "Sigma" && (skipped.has(r) || (book.tlds[r]?.$ === "ADT" && !(r in ADTS) && r !== "Sigma" && !emitted.has(r))));
    if (bad) { skipped.set(k, "uses " + bad); continue; }
    try { const src = inductive(k, d0); emitted.set(k, src); lines.push(src); }
    catch (e) { skipped.set(k, (e as Error).message.slice(0, 80)); }
    continue;
  }
  const d: T = book.tlds[k];
  const Tl = low(d.T);
  qpos[k] = params(Tl);
  const acc = new Set<string>();
  refs(Tl, acc);
  if (d.v) refs(low(d.v), acc);
  const bad = [...acc].find((r) => r !== "Word" && r !== "Pair" && r !== "Sigma" && (skipped.has(r) || (book.tlds[r]?.$ === "ADT" && !(r in ADTS) && r !== "Sigma" && !emitted.has(r))));
  if (bad) { skipped.set(k, "uses " + bad); continue; }
  if (!d.v) { skipped.set(k, "law without proof"); continue; }
  try {
    let ret = Tl;
    while (ret.$ === "All") ret = ret.B;
    dataVars = new Set<number>();
    holds(Tl, dataVars);
    if (d.v) holds(low(d.v), dataVars);
    ren.clear();
    let head = ret;
    while (head.$ === "App") head = head.f;
    const kw = ret.$ === "Eql" || (head.$ === "Ref" && props.has(head.k)) ? "theorem" : "def";
    let body = low(d.v);
    while (body.$ === "Lam") body = body.f;
    let tyS = tm(Tl);
    if (ret.$ === "Typ" && body.$ === "Eql") { tyS = tyS.replace(/ Type\)*$/, (m: string) => m.replace("Type", "Prop")); props.add(k); }
    const src = `${kw} ${lname(k)} : ${tyS} :=\n  ${tm(low(d.v))}\n`;
    emitted.set(k, src);
    lines.push(src);
    if (mc && mc[mc.length - 1] === k) lines.push("end", "");
  } catch (e) {
    skipped.set(k, (e as Error).message.slice(0, 80));
  }
}
lines.push("end Bend", "");
for (const k of new Set(rootDefs)) if (emitted.has(k)) lines.push(`#print axioms Bend.${lname(k)}`);
const text = lines.join("\n");
if (out) fs.writeFileSync(out, text); else console.log(text);
console.error(`translated ${emitted.size} defs; skipped ${skipped.size}`);
for (const k of (process.env.ALLSKIP ? [...skipped.keys()] : rootDefs)) if (skipped.has(k)) console.error(`  skipped ${k}: ${skipped.get(k)}`);
