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

Lean checks it in about 5 s. Its only axioms are `propext` and `Quot.sound`; there is no `sorry`. The compiled Bend version (`bench/taylor_bench.bend`) runs 2^20 shifts in about 0.7 s on one core. Lean's in-place version (`bench/TaylorBench.lean`) takes about 5 s.

## How the translation works

| Bend core | Lean |
|---|---|
| λ-match chain | `fun x => match x with …`; default arms expanded into the remaining constructors |
| `%e : P; f` | `Eq.mp (congrArg (fun x => P) e) f` |
| `{==}` | `rfl` |
| empty match | `nomatch` |
| `Nat`, `Bool`, `List`, `Pair`, `Unit`, `Empty` | Lean's own types |
| `Word(n)`, U32 literals | the indexed type `BWord n`, the literal's bits |
| user datatypes | `inductive` |
| quantities | erased |
| cycles of definitions | broken by inlining the non-recursive members |

Definitions it can't translate (IO, String, F32, other indexed types), and everything that uses them, are skipped and reported.

## Coverage on Bend's own proof tests

`scripts/corpus.sh` runs every file in Bend's `tests/proof` (`results/corpus.tsv`, Bend `0e2f38f7`, Lean 4.35):

- 43 of 121 files translate completely and re-check in Lean, with no axioms;
- 504 results are axiom-free;
- the rest hit untranslated features or Lean errors in specific constructs, listed in the results file.

## Requirements

[Bun](https://bun.sh), a Bend checkout (`BEND_DIR`) and Lean 4.35. Bend changes quickly; the translator reads `bend.ts`'s internal terms and was last run against bendlang/bend `0e2f38f7`.
