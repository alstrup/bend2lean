# poly: dense univariate polynomials over Nat, coefficients lowest degree
# first. add, scale, mul, Horner evaluation and the Taylor shift
# p(x) -> p(x+1), the core step of Descartes / Vincent-Collins-Akritas
# real root isolation. LAWS.bend states that each operation means what it
# says under eval; PROOF.bend proves it.

import Base
import ./ARRLAWS.bend as A

def add(p: List<&2, Nat>, q: List<&2, Nat>) -> List<&2, Nat>:
  match p q:
    case Nil{} _:
      q
    case Con{a, ps} Nil{}:
      Con{a, ps}
    case Con{a, ps} Con{b, qs}:
      Con{Nat.add(a, b), add(ps, qs)}

def scale(+c: Nat, p: List<&2, Nat>) -> List<&2, Nat>:
  match p:
    case Nil{}:
      Nil{}
    case Con{a, ps}:
      Con{Nat.mul(c, a), scale(c, ps)}

def mul(p: List<&2, Nat>, +q: List<&2, Nat>) -> List<&2, Nat>:
  match p:
    case Nil{}:
      Nil{}
    case Con{a, ps}:
      add(scale(a, q), Con{0n, mul(ps, q)})

def eval(p: List<&2, Nat>, +x: Nat) -> Nat:
  match p:
    case Nil{}:
      0n
    case Con{a, ps}:
      Nat.add(a, Nat.mul(x, eval(ps, x)))

# p(x+1), by Horner: (a + x*q(x)) at x+1 is a + q(x+1) + x*q(x+1)
def shift1(p: List<&2, Nat>) -> List<&2, Nat>:
  match p:
    case Nil{}:
      Nil{}
    case Con{a, ps}:
      +s = shift1(ps)
      add(Con{a, Nil{}}, add(s, Con{0n, s}))

# Suffix sums. One pass of a[j] += a[j+1] (j counting down) leaves the
# suffix sums S0, S1, ..., which is synthetic division by (x - 1):
# p(x) = S0 + (x-1)*q(x), q = [S1, S2, ...], so p(y+1) = S0 + y*q(y+1).

# (S0, q) for the polynomial a :: ps
def suffix.k(a: Nat, r: Nat & List<&2, Nat>) -> Nat & List<&2, Nat>:
  (+h, t) = r
  (Nat.add(a, h), Con{h, t})

def suffix(ps: List<&2, Nat>, a: Nat) -> Nat & List<&2, Nat>:
  match ps:
    case Nil{}:
      (a, Nil{})
    case Con{b, qs}:
      suffix.k(a, suffix(qs, b))

# The same shift as a template over the container: ~get and ~set are
# inlined at compile time. Instantiated with Array it is the fast version;
# with a list it is the model the proof reasons about.

def tstep.k(~C: Type, ~set: C -> Nat -> Nat -> C, +i: Nat, s: Nat, r: C & Nat) -> C & Nat:
  (b, x) = r
  +v = Nat.add(x, s)
  (set(b, i, v), v)

def tstep(~C: Type, ~get: C -> Nat -> C & Nat, ~set: C -> Nat -> Nat -> C, r: C & Nat, +i: Nat) -> C & Nat:
  (a, s) = r
  tstep.k(~C, ~set, i, s, get(a, i))

def tloop(~C: Type, ~get: C -> Nat -> C & Nat, ~set: C -> Nat -> Nat -> C, k: Nat, r: C & Nat, +j: Nat) -> C & Nat:
  match k:
    case 0n:
      r
    case 1n++q:
      tloop(~C, ~get, ~set, q, tstep(~C, ~get, ~set, r, Nat.add(j, q)), j)

def tpass(~C: Type, ~get: C -> Nat -> C & Nat, ~set: C -> Nat -> Nat -> C, +c: Nat, a: C, +j: Nat) -> C & Nat:
  tloop(~C, ~get, ~set, c, get(a, Nat.add(j, c)), j)

def tshift(~C: Type, ~get: C -> Nat -> C & Nat, ~set: C -> Nat -> Nat -> C, +c: Nat, a: C, +j: Nat) -> C:
  match c:
    case 0n:
      a
    case 1n++d:
      tshift(~C, ~get, ~set, d, Pair.fst(C, Nat, tpass(~C, ~get, ~set, 1n+d, a, j)), 1n+j)

def arr_get(a: Array<Nat>, +i: Nat) -> Array<Nat> & Nat:
  Array.get(Nat, a, U32.from_nat(i))

def arr_set(a: Array<Nat>, +i: Nat, v: Nat) -> Array<Nat>:
  Array.set(Nat, a, U32.from_nat(i), v)

def ashift(+c: Nat, a: Array<Nat>, +j: Nat) -> Array<Nat>:
  tshift(~Array<Nat>, ~(a => i => arr_get(a, i)), ~(a => i => v => arr_set(a, i, v)), c, a, j)

# The list model: the same template over a list, by position.

def lst_get(+l: List<&2, Nat>, +i: Nat) -> List<&2, Nat> & Nat:
  (l, A.nth(l, i))

def lshift(+c: Nat, l: List<&2, Nat>, +j: Nat) -> List<&2, Nat>:
  tshift(~List<&2, Nat>, ~(l => i => lst_get(l, i)), ~(l => i => v => A.upd(l, i, v)), c, l, j)
