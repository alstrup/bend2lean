# PURE: list and Nat facts the list-model proof uses, all on live values.

import Base
import ./main.bend as P
import ./PROOF.bend as N

# Suffix sums with a carry (pure lists)
# -------------------------------------

def app1(xs: List<&2, Nat>, +s: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Con{s, Nil{}}
    case Con{x, t}:
      Con{x, app1(t, s)}

# the suffix sums of xs ++ [s]: (first sum, the rest)
def sufc(xs: List<&2, Nat>, +s: Nat) -> Nat & List<&2, Nat>:
  match xs:
    case Nil{}:
      (s, Nil{})
    case Con{x, t}:
      P.suffix.k(x, sufc(t, s))

def eta(r: Nat & List<&2, Nat>) -> {(Pair.fst(Nat, List<&2, Nat>, r), Pair.snd(Nat, List<&2, Nat>, r)) == r : Nat & List<&2, Nat>}:
  (h, t) = r
  {==}

def H(xs: List<&2, Nat>, +s: Nat) -> Nat:
  Pair.fst(Nat, List<&2, Nat>, sufc(xs, s))

def T(xs: List<&2, Nat>, +s: Nat) -> List<&2, Nat>:
  Pair.snd(Nat, List<&2, Nat>, sufc(xs, s))

# synthetic division by (x - 1): p(1+y) = S0 + y * q(1+y)
def syn(xs: List<&2, Nat>, +s: Nat, +y: Nat) -> {P.eval(app1(xs, s), 1n+y) == Nat.add(H(xs, s), Nat.mul(y, P.eval(T(xs, s), 1n+y))) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %eta(sufc(t, s)) : {Nat.add(x, Nat.add(P.eval(app1(t, s), 1n+y), Nat.mul(y, P.eval(app1(t, s), 1n+y)))) == Nat.add(Pair.fst(Nat, List<&2, Nat>, P.suffix.k(x, _)), Nat.mul(y, P.eval(Pair.snd(Nat, List<&2, Nat>, P.suffix.k(x, _)), 1n+y))) : Nat}
      %Equal.sym(Nat, P.eval(app1(t, s), 1n+y), Nat.add(H(t, s), Nat.mul(y, P.eval(T(t, s), 1n+y))), syn(t, s, y)) : {Nat.add(x, Nat.add(_, Nat.mul(y, _))) == Nat.add(Nat.add(x, H(t, s)), Nat.mul(y, Nat.add(H(t, s), Nat.add(P.eval(T(t, s), 1n+y), Nat.mul(y, P.eval(T(t, s), 1n+y)))))) : Nat}
      %N.mul_fold(y, H(t, s), Nat.mul(y, P.eval(T(t, s), 1n+y))) : {Nat.add(x, Nat.add(Nat.add(H(t, s), Nat.mul(y, P.eval(T(t, s), 1n+y))), _)) == Nat.add(Nat.add(x, H(t, s)), Nat.mul(y, Nat.add(H(t, s), Nat.add(P.eval(T(t, s), 1n+y), Nat.mul(y, P.eval(T(t, s), 1n+y)))))) : Nat}
      %N.mul_fold(y, H(t, s), Nat.add(P.eval(T(t, s), 1n+y), Nat.mul(y, P.eval(T(t, s), 1n+y)))) : {Nat.add(x, Nat.add(Nat.add(H(t, s), Nat.mul(y, P.eval(T(t, s), 1n+y))), Nat.add(Nat.mul(y, H(t, s)), Nat.mul(y, Nat.mul(y, P.eval(T(t, s), 1n+y)))))) == Nat.add(Nat.add(x, H(t, s)), _) : Nat}
      %N.mul_fold(y, P.eval(T(t, s), 1n+y), Nat.mul(y, P.eval(T(t, s), 1n+y))) : {Nat.add(x, Nat.add(Nat.add(H(t, s), Nat.mul(y, P.eval(T(t, s), 1n+y))), Nat.add(Nat.mul(y, H(t, s)), Nat.mul(y, Nat.mul(y, P.eval(T(t, s), 1n+y)))))) == Nat.add(Nat.add(x, H(t, s)), Nat.add(Nat.mul(y, H(t, s)), _)) : Nat}
      %N.add_assoc(H(t, s), Nat.mul(y, P.eval(T(t, s), 1n+y)), Nat.add(Nat.mul(y, H(t, s)), Nat.mul(y, Nat.mul(y, P.eval(T(t, s), 1n+y))))) : {Nat.add(x, _) == Nat.add(Nat.add(x, H(t, s)), Nat.add(Nat.mul(y, H(t, s)), Nat.add(Nat.mul(y, P.eval(T(t, s), 1n+y)), Nat.mul(y, Nat.mul(y, P.eval(T(t, s), 1n+y)))))) : Nat}
      %N.add_swap(Nat.mul(y, P.eval(T(t, s), 1n+y)), Nat.mul(y, H(t, s)), Nat.mul(y, Nat.mul(y, P.eval(T(t, s), 1n+y)))) : {Nat.add(x, Nat.add(H(t, s), Nat.add(Nat.mul(y, P.eval(T(t, s), 1n+y)), Nat.add(Nat.mul(y, H(t, s)), Nat.mul(y, Nat.mul(y, P.eval(T(t, s), 1n+y))))))) == Nat.add(Nat.add(x, H(t, s)), _) : Nat}
      %N.add_assoc(x, H(t, s), Nat.add(Nat.mul(y, P.eval(T(t, s), 1n+y)), Nat.add(Nat.mul(y, H(t, s)), Nat.mul(y, Nat.mul(y, P.eval(T(t, s), 1n+y)))))) : {Nat.add(x, Nat.add(H(t, s), Nat.add(Nat.mul(y, P.eval(T(t, s), 1n+y)), Nat.add(Nat.mul(y, H(t, s)), Nat.mul(y, Nat.mul(y, P.eval(T(t, s), 1n+y))))))) == _ : Nat}
      {==}

# Index arithmetic
# ----------------

def add_one(+j: Nat) -> {1n+j == Nat.add(j, 1n) : Nat}:
  %N.add_succ(j, 0n) : {1n+j == _ : Nat}
  %N.add_zero(j) : {1n+j == 1n+_ : Nat}
  {==}

# suffix sums of w ++ [x] with carry s: those of w with carry x+s, then s
def sufc_snoc(w: List<&2, Nat>, +x: Nat, +s: Nat) -> {(H(w, Nat.add(x, s)), app1(T(w, Nat.add(x, s)), s)) == sufc(app1(w, x), s) : Nat & List<&2, Nat>}:
  match w:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      %sufc_snoc(t, x, s) : {(H(Con{y, t}, Nat.add(x, s)), app1(T(Con{y, t}, Nat.add(x, s)), s)) == P.suffix.k(y, _) : Nat & List<&2, Nat>}
      %eta(sufc(t, Nat.add(x, s))) : {(Pair.fst(Nat, List<&2, Nat>, P.suffix.k(y, _)), app1(Pair.snd(Nat, List<&2, Nat>, P.suffix.k(y, _)), s)) == P.suffix.k(y, (H(t, Nat.add(x, s)), app1(T(t, Nat.add(x, s)), s))) : Nat & List<&2, Nat>}
      {==}

