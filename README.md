# bend2lean

Translate [Bend](https://github.com/bendlang/bend) definitions, laws and proofs into Lean 4, so Lean's kernel re-checks them. A Bend theorem becomes a Lean theorem without trusting Bend's checker.

```bash
BEND_DIR=../bend bun bend2lean.ts file.bend out.lean   # then: lean out.lean
```

`bend2lean.ts` loads a file with Bend's own loader (`bend2/bend.ts`), translates every definition the file needs (Base included), and ends the Lean file with `#print axioms` for each one.

## Worked example: a fast Taylor shift, proved in Bend, checked in Lean

`examples/taylor/` holds a Taylor shift `p(x) ↦ p(x+1)` on coefficient lists. It is written once as a template over `get`/`set` and run in place on Base's `Array`. The Bend proofs show that it computes `p(x+1)`; nothing is assumed, and `--verdict` passes:

| file | proves |
|---|---|
| `PROOF.bend`, `LAWS.bend` | polynomial add/scale/mul/eval laws, Nat ring lemmas |
| `PURE.bend` | synthetic division by (x−1), suffix sums |
| `LISTPROOF.bend` | the template run on a list computes the shifted region (`shift_r`, `ev_lsp`) |
| `ARRLAWS.bend` | `Array.get` / `Array.set` on perfect trees, and the U32 facts behind them (also bendlang/bend#2213) |
| `SIMPROOF2.bend` | the run on `Array` tracks the list run step by step (`ashift_ok`) |

`scripts/build.sh` translates the chain (266 definitions) and appends `lean/FastBridge.lean`. That file ties Bend's `Nat`, list and evaluation functions to Lean's and states:

```lean
theorem Bend.fast_taylor_shift (c : Nat) (pre R rest : List Nat) (hR : R.length = c + 1)
    (hlen : 64 ≤ (pre ++ (R.reverse ++ rest)).length) (hfit : pre.length + c ≤ 63) :
    ∃ Q : List Nat,
      «main:ashift» c («ARRLAWS:build» 6 (pre ++ (R.reverse ++ rest))) pre.length
        = «ARRLAWS:build» 6 (pre ++ (Q ++ rest)) ∧
      ∀ y, horner Q y = horner R.reverse (y + 1)
```

Lean checks it in about 5 s. Its only axioms are Lean's standard `propext` and `Quot.sound`; there is no `sorry`. The compiled Bend version (`bench/taylor_bench.bend`) runs 2^20 shifts in about 0.7 s on one core. Lean's in-place version (`bench/TaylorBench.lean`) takes about 5 s.

## How the translation works

| Bend core | Lean |
|---|---|
| λ-match chain | `fun x => match x with …`; default arms expanded into the remaining constructors, known constructors resolved statically |
| equality `{a == b : T}` | `Beq a b`, a Type-valued equality (Bend's equalities are data: they go in pairs and type families) |
| `%e : P; f` | `Beq.J (fun x ev => P) e f`, Bend's rewrite rule exactly |
| `{==}` | `Beq.refl` |
| empty match | `nomatch` |
| `Nat`, `Bool`, `List`, `Unit`, `Empty` | Lean's own types |
| `Pair`, `Sigma`, `Exists` | `Σ` |
| `Word(n)`, U32 / F32 / String literals | the indexed type `BWord n`, the literal's bits or characters |
| user datatypes | universe-polymorphic `inductive`; value parameters, and type parameters a recursive field changes, become indices; mutual types go in a `mutual` block |
| `Type` | `Type _`, so Lean solves the levels of Bend's single universe |
| quantities | erased |
| cycles of definitions | broken by inlining the non-recursive members within the cycle |
| lexicographic recursion on two `Nat`s (Ackermann) | nested `Nat.rec`, so the equations still hold by definition |
| a literal in a recursive call, pinned by the match (`case 300n: down(299n)`) | the pattern variable that holds it |

`IO` code is effectful, not proof: it and everything that uses it are skipped and reported as effect code. Other unsupported definitions are skipped and reported as well.

The bridge back to Lean's `Eq` is `Beq.toEq` / `Beq.ofEq` (see `lean/FastBridge.lean`).

## Coverage on Bend's own proof tests

`scripts/corpus.sh` translates every file in Bend's `tests/proof` and scores it against the test's own expected verdict (`results/corpus.tsv`, Bend `0e2f38f7`, Lean 4.35):

| | |
|---|---|
| positive tests (Bend accepts) that Lean re-checks completely | **86 / 86** |
| negative tests (Bend rejects) that Lean rejects too | **33 / 35** |
| negative tests where Lean accepts an invalid proof | **0** |

The two other negative tests are rejected by Bend for reasons outside the proofs:
- `PROOF` is rejected only for its `@unsafe` IO code; its proofs check in both.
- `LAWS` is rejected only for an open law, which the translator skips.

## Requirements

[Bun](https://bun.sh), a Bend checkout (`BEND_DIR`) and Lean 4.35. Bend changes quickly; the translator reads `bend.ts`'s internal terms and was last run against bendlang/bend `0e2f38f7`.
