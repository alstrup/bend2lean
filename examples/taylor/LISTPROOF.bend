# LISTPROOF: the template shift, run on a list (main.bend lshift), turns
# the region j..j+c of the list into the Taylor shift of its coefficients.
# Everything here is a live list, so ordinary induction applies.

import Base
import ./main.bend as P
import ./PROOF.bend as N
import ./PURE.bend as U
import ./ARRLAWS.bend as A

# List vocabulary
# ---------------

def len(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, t}:
      1n+len(t)

def app(xs: List<&2, Nat>, ys: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      ys
    case Con{x, t}:
      Con{x, app(t, ys)}

def rev(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      U.app1(rev(t), x)

# The template, instantiated at lists (the same instance lshift uses)
def LL(k: Nat, r: List<&2, Nat> & Nat, +j: Nat) -> List<&2, Nat> & Nat:
  P.tloop(~List<&2, Nat>, ~(l => i => P.lst_get(l, i)), ~(l => i => v => A.upd(l, i, v)), k, r, j)

def LP(+c: Nat, a: List<&2, Nat>, +j: Nat) -> List<&2, Nat> & Nat:
  P.tpass(~List<&2, Nat>, ~(l => i => P.lst_get(l, i)), ~(l => i => v => A.upd(l, i, v)), c, a, j)

# Position lemmas
# ---------------

def nth_off(pre: List<&2, Nat>, +m: List<&2, Nat>, +q: Nat) -> {A.nth(m, q) == A.nth(app(pre, m), Nat.add(len(pre), q)) : Nat}:
  match pre:
    case Nil{}:
      {==}
    case Con{x, t}:
      nth_off(t, m, q)

def upd_off(pre: List<&2, Nat>, +m: List<&2, Nat>, +q: Nat, +v: Nat) -> {app(pre, A.upd(m, q, v)) == A.upd(app(pre, m), Nat.add(len(pre), q), v) : List<&2, Nat>}:
  match pre:
    case Nil{}:
      {==}
    case Con{+x, t}:
      %upd_off(t, m, q, v) : {Con{x, app(t, A.upd(m, q, v))} == Con{x, _} : List<&2, Nat>}
      {==}

def app_app1(u: List<&2, Nat>, +y: Nat, +r: List<&2, Nat>) -> {app(u, Con{y, r}) == app(U.app1(u, y), r) : List<&2, Nat>}:
  match u:
    case Nil{}:
      {==}
    case Con{+x, t}:
      %app_app1(t, y, r) : {Con{x, app(t, Con{y, r})} == Con{x, _} : List<&2, Nat>}
      {==}

def nth_at(w: List<&2, Nat>, +x: Nat, +r: List<&2, Nat>) -> {x == A.nth(app(U.app1(w, x), r), len(w)) : Nat}:
  match w:
    case Nil{}:
      {==}
    case Con{y, t}:
      nth_at(t, x, r)

def upd_at(w: List<&2, Nat>, +x: Nat, +r: List<&2, Nat>, +v: Nat) -> {app(U.app1(w, v), r) == A.upd(app(U.app1(w, x), r), len(w), v) : List<&2, Nat>}:
  match w:
    case Nil{}:
      {==}
    case Con{+y, t}:
      %upd_at(t, x, r, v) : {Con{y, app(U.app1(t, v), r)} == Con{y, _} : List<&2, Nat>}
      {==}

def len_app1(w: List<&2, Nat>, +x: Nat) -> {1n+len(w) == len(U.app1(w, x)) : Nat}:
  match w:
    case Nil{}:
      {==}
    case Con{y, t}:
      %len_app1(t, x) : {2n+len(t) == 1n+_ : Nat}
      {==}

def len_rev(xs: List<&2, Nat>) -> {len(rev(xs)) == len(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %len_app1(rev(t), x) : {_ == 1n+len(t) : Nat}
      %len_rev(t) : {1n+len(rev(t)) == 1n+_ : Nat}
      {==}

# The loop
# --------

# over the region rev(rw) ++ [s] at position len(pre), carrying s: the
# region becomes its suffix sums, and the loop answers the first one
def loop_r(rw: List<&2, Nat>, +pre: List<&2, Nat>, +s: Nat, +rest: List<&2, Nat>) -> {(app(pre, app(Con{U.H(rev(rw), s), U.T(rev(rw), s)}, rest)), U.H(rev(rw), s)) == LL(len(rw), (app(pre, app(U.app1(rev(rw), s), rest)), s), len(pre)) : List<&2, Nat> & Nat}:
  match rw:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %nth_off(pre, app(U.app1(U.app1(rev(t), x), s), rest), len(t)) : {(app(pre, app(Con{U.H(U.app1(rev(t), x), s), U.T(U.app1(rev(t), x), s)}, rest)), U.H(U.app1(rev(t), x), s)) == LL(len(t), (A.upd(app(pre, app(U.app1(U.app1(rev(t), x), s), rest)), Nat.add(len(pre), len(t)), Nat.add(_, s)), Nat.add(_, s)), len(pre)) : List<&2, Nat> & Nat}
      %app_app1(U.app1(rev(t), x), s, rest) : {(app(pre, app(Con{U.H(U.app1(rev(t), x), s), U.T(U.app1(rev(t), x), s)}, rest)), U.H(U.app1(rev(t), x), s)) == LL(len(t), (A.upd(app(pre, app(U.app1(U.app1(rev(t), x), s), rest)), Nat.add(len(pre), len(t)), Nat.add(A.nth(_, len(t)), s)), Nat.add(A.nth(_, len(t)), s)), len(pre)) : List<&2, Nat> & Nat}
      %len_rev(t) : {(app(pre, app(Con{U.H(U.app1(rev(t), x), s), U.T(U.app1(rev(t), x), s)}, rest)), U.H(U.app1(rev(t), x), s)) == LL(len(t), (A.upd(app(pre, app(U.app1(U.app1(rev(t), x), s), rest)), Nat.add(len(pre), len(t)), Nat.add(A.nth(app(U.app1(rev(t), x), Con{s, rest}), _), s)), Nat.add(A.nth(app(U.app1(rev(t), x), Con{s, rest}), _), s)), len(pre)) : List<&2, Nat> & Nat}
      %nth_at(rev(t), x, Con{s, rest}) : {(app(pre, app(Con{U.H(U.app1(rev(t), x), s), U.T(U.app1(rev(t), x), s)}, rest)), U.H(U.app1(rev(t), x), s)) == LL(len(t), (A.upd(app(pre, app(U.app1(U.app1(rev(t), x), s), rest)), Nat.add(len(pre), len(t)), Nat.add(_, s)), Nat.add(_, s)), len(pre)) : List<&2, Nat> & Nat}
      %upd_off(pre, app(U.app1(U.app1(rev(t), x), s), rest), len(t), Nat.add(x, s)) : {(app(pre, app(Con{U.H(U.app1(rev(t), x), s), U.T(U.app1(rev(t), x), s)}, rest)), U.H(U.app1(rev(t), x), s)) == LL(len(t), (_, Nat.add(x, s)), len(pre)) : List<&2, Nat> & Nat}
      %app_app1(U.app1(rev(t), x), s, rest) : {(app(pre, app(Con{U.H(U.app1(rev(t), x), s), U.T(U.app1(rev(t), x), s)}, rest)), U.H(U.app1(rev(t), x), s)) == LL(len(t), (app(pre, A.upd(_, len(t), Nat.add(x, s))), Nat.add(x, s)), len(pre)) : List<&2, Nat> & Nat}
      %len_rev(t) : {(app(pre, app(Con{U.H(U.app1(rev(t), x), s), U.T(U.app1(rev(t), x), s)}, rest)), U.H(U.app1(rev(t), x), s)) == LL(len(t), (app(pre, A.upd(app(U.app1(rev(t), x), Con{s, rest}), _, Nat.add(x, s))), Nat.add(x, s)), len(pre)) : List<&2, Nat> & Nat}
      %upd_at(rev(t), x, Con{s, rest}, Nat.add(x, s)) : {(app(pre, app(Con{U.H(U.app1(rev(t), x), s), U.T(U.app1(rev(t), x), s)}, rest)), U.H(U.app1(rev(t), x), s)) == LL(len(t), (app(pre, _), Nat.add(x, s)), len(pre)) : List<&2, Nat> & Nat}
      %loop_r(t, pre, Nat.add(x, s), Con{s, rest}) : {(app(pre, app(Con{U.H(U.app1(rev(t), x), s), U.T(U.app1(rev(t), x), s)}, rest)), U.H(U.app1(rev(t), x), s)) == _ : List<&2, Nat> & Nat}
      %U.sufc_snoc(rev(t), x, s) : {(app(pre, app(Con{Pair.fst(Nat, List<&2, Nat>, _), Pair.snd(Nat, List<&2, Nat>, _)}, rest)), Pair.fst(Nat, List<&2, Nat>, _)) == (app(pre, app(Con{U.H(rev(t), Nat.add(x, s)), U.T(rev(t), Nat.add(x, s))}, Con{s, rest})), U.H(rev(t), Nat.add(x, s))) : List<&2, Nat> & Nat}
      %app_app1(U.T(rev(t), Nat.add(x, s)), s, rest) : {(app(pre, Con{U.H(rev(t), Nat.add(x, s)), _}), U.H(rev(t), Nat.add(x, s))) == (app(pre, app(Con{U.H(rev(t), Nat.add(x, s)), U.T(rev(t), Nat.add(x, s))}, Con{s, rest})), U.H(rev(t), Nat.add(x, s))) : List<&2, Nat> & Nat}
      {==}

# the pass reads its carry from slot len(pre)+len(rw), then runs the loop
def pass_r(+rw: List<&2, Nat>, +pre: List<&2, Nat>, +s: Nat, +rest: List<&2, Nat>) -> {(app(pre, app(Con{U.H(rev(rw), s), U.T(rev(rw), s)}, rest)), U.H(rev(rw), s)) == LP(len(rw), app(pre, app(U.app1(rev(rw), s), rest)), len(pre)) : List<&2, Nat> & Nat}:
  %nth_off(pre, app(U.app1(rev(rw), s), rest), len(rw)) : {(app(pre, app(Con{U.H(rev(rw), s), U.T(rev(rw), s)}, rest)), U.H(rev(rw), s)) == LL(len(rw), (app(pre, app(U.app1(rev(rw), s), rest)), _), len(pre)) : List<&2, Nat> & Nat}
  %len_rev(rw) : {(app(pre, app(Con{U.H(rev(rw), s), U.T(rev(rw), s)}, rest)), U.H(rev(rw), s)) == LL(len(rw), (app(pre, app(U.app1(rev(rw), s), rest)), A.nth(app(U.app1(rev(rw), s), rest), _)), len(pre)) : List<&2, Nat> & Nat}
  %nth_at(rev(rw), s, rest) : {(app(pre, app(Con{U.H(rev(rw), s), U.T(rev(rw), s)}, rest)), U.H(rev(rw), s)) == LL(len(rw), (app(pre, app(U.app1(rev(rw), s), rest)), _), len(pre)) : List<&2, Nat> & Nat}
  loop_r(rw, pre, s, rest)

# Reversal and lengths
# --------------------

def rev_app1(xs: List<&2, Nat>, +x: Nat) -> {Con{x, rev(xs)} == rev(U.app1(xs, x)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      %rev_app1(t, x) : {Con{x, rev(Con{y, t})} == U.app1(_, y) : List<&2, Nat>}
      {==}

def rev_rev(xs: List<&2, Nat>) -> {rev(rev(xs)) == xs : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %rev_app1(rev(t), x) : {_ == Con{x, t} : List<&2, Nat>}
      %rev_rev(t) : {Con{x, rev(rev(t))} == Con{x, _} : List<&2, Nat>}
      {==}

def len_T(w: List<&2, Nat>, +s: Nat) -> {len(w) == len(U.T(w, s)) : Nat}:
  match w:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %U.eta(U.sufc(t, s)) : {1n+len(t) == len(Pair.snd(Nat, List<&2, Nat>, P.suffix.k(x, _))) : Nat}
      %len_T(t, s) : {1n+len(t) == 1n+_ : Nat}
      {==}

def pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+q:
      q

def sinj(-a: Nat, -b: Nat, e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, n => pred(n), 1n+a, 1n+b, e)

def disc(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+q:
      Unit

def zne(-q: Nat, e: {0n == 1n+q : Nat}) -> Empty:
  %Equal.sym(Nat, 0n, 1n+q, e) : disc(_)
  Unit{}

def efq(-G: Type, x: Empty) -> G:
  match x:

# The shift
# ---------

# the Taylor shift of the region rev(R), by passes: the first suffix sum,
# then the shift of the rest of the sums
def lsp(c: Nat, R: List<&2, Nat>) -> List<&2, Nat>:
  match c:
    case 0n:
      rev(R)
    case 1n+d:
      match R:
        case Nil{}:
          Nil{}
        case Con{+s, +rw}:
          Con{U.H(rev(rw), s), lsp(d, rev(U.T(rev(rw), s)))}

def TSH(+c: Nat, a: List<&2, Nat>, +j: Nat) -> List<&2, Nat>:
  P.tshift(~List<&2, Nat>, ~(l => i => P.lst_get(l, i)), ~(l => i => v => A.upd(l, i, v)), c, a, j)

def hlen(+rw: List<&2, Nat>, +s: Nat, -d: Nat, +hl: {len(rw) == 1n+d : Nat}) -> {len(rev(U.T(rev(rw), s))) == 1n+d : Nat}:
  Equal.trans(Nat, len(rev(U.T(rev(rw), s))), len(U.T(rev(rw), s)), 1n+d, len_rev(U.T(rev(rw), s)),
    Equal.trans(Nat, len(U.T(rev(rw), s)), len(rev(rw)), 1n+d, Equal.sym(Nat, len(rev(rw)), len(U.T(rev(rw), s)), len_T(rev(rw), s)),
      Equal.trans(Nat, len(rev(rw)), len(rw), 1n+d, len_rev(rw), hl)))

# the list model shifts the region in place, leaving the rest alone
def shift_r(+c: Nat, +pre: List<&2, Nat>, +R: List<&2, Nat>, +rest: List<&2, Nat>, +hR: {len(R) == 1n+c : Nat}) -> {app(pre, app(lsp(c, R), rest)) == P.lshift(c, app(pre, app(rev(R), rest)), len(pre)) : List<&2, Nat>}:
  match c:
    case 0n:
      {==}
    case 1n++d:
      match R:
        case Nil{}:
          efq({app(pre, app(lsp(1n+d, Nil{}), rest)) == P.lshift(1n+d, app(pre, app(rev(Nil{}), rest)), len(pre)) : List<&2, Nat>}, zne(1n+d, hR))
        case Con{+s, +rw}:
          +hl = sinj(len(rw), 1n+d, hR)
          %hl : {app(pre, app(Con{U.H(rev(rw), s), lsp(d, rev(U.T(rev(rw), s)))}, rest)) == TSH(d, Pair.fst(List<&2, Nat>, Nat, LP(_, app(pre, app(U.app1(rev(rw), s), rest)), len(pre))), 1n+len(pre)) : List<&2, Nat>}
          %pass_r(rw, pre, s, rest) : {app(pre, app(Con{U.H(rev(rw), s), lsp(d, rev(U.T(rev(rw), s)))}, rest)) == TSH(d, Pair.fst(List<&2, Nat>, Nat, _), 1n+len(pre)) : List<&2, Nat>}
          %Equal.sym(List<&2, Nat>, app(pre, Con{U.H(rev(rw), s), app(U.T(rev(rw), s), rest)}), app(U.app1(pre, U.H(rev(rw), s)), app(U.T(rev(rw), s), rest)), app_app1(pre, U.H(rev(rw), s), app(U.T(rev(rw), s), rest))) : {app(pre, app(Con{U.H(rev(rw), s), lsp(d, rev(U.T(rev(rw), s)))}, rest)) == TSH(d, _, 1n+len(pre)) : List<&2, Nat>}
          %rev_rev(U.T(rev(rw), s)) : {app(pre, app(Con{U.H(rev(rw), s), lsp(d, rev(U.T(rev(rw), s)))}, rest)) == TSH(d, app(U.app1(pre, U.H(rev(rw), s)), app(_, rest)), 1n+len(pre)) : List<&2, Nat>}
          %Equal.sym(Nat, 1n+len(pre), len(U.app1(pre, U.H(rev(rw), s))), len_app1(pre, U.H(rev(rw), s))) : {app(pre, app(Con{U.H(rev(rw), s), lsp(d, rev(U.T(rev(rw), s)))}, rest)) == TSH(d, app(U.app1(pre, U.H(rev(rw), s)), app(rev(rev(U.T(rev(rw), s))), rest)), _) : List<&2, Nat>}
          %shift_r(d, U.app1(pre, U.H(rev(rw), s)), rev(U.T(rev(rw), s)), rest, hlen(rw, s, d, hl)) : {app(pre, app(Con{U.H(rev(rw), s), lsp(d, rev(U.T(rev(rw), s)))}, rest)) == _ : List<&2, Nat>}
          %app_app1(pre, U.H(rev(rw), s), app(lsp(d, rev(U.T(rev(rw), s))), rest)) : {app(pre, app(Con{U.H(rev(rw), s), lsp(d, rev(U.T(rev(rw), s)))}, rest)) == _ : List<&2, Nat>}
          {==}

# the shifted region evaluates at y to the region at y+1
def ev_lsp(+c: Nat, +R: List<&2, Nat>, +y: Nat, +hR: {len(R) == 1n+c : Nat}) -> {P.eval(lsp(c, R), y) == P.eval(rev(R), 1n+y) : Nat}:
  match c:
    case 0n:
      match R:
        case Nil{}:
          efq({P.eval(lsp(0n, Nil{}), y) == P.eval(rev(Nil{}), 1n+y) : Nat}, zne(0n, hR))
        case Con{+s, +rw}:
          match rw:
            case Nil{}:
              {==}
            case Con{+z, +u}:
              efq({P.eval(lsp(0n, Con{s, Con{z, u}}), y) == P.eval(rev(Con{s, Con{z, u}}), 1n+y) : Nat}, zne(len(u), Equal.sym(Nat, 1n+len(u), 0n, sinj(1n+len(u), 0n, hR))))
    case 1n++d:
      match R:
        case Nil{}:
          efq({P.eval(lsp(1n+d, Nil{}), y) == P.eval(rev(Nil{}), 1n+y) : Nat}, zne(1n+d, hR))
        case Con{+s, +rw}:
          +hl = sinj(len(rw), 1n+d, hR)
          %Equal.sym(Nat, P.eval(U.app1(rev(rw), s), 1n+y), Nat.add(U.H(rev(rw), s), Nat.mul(y, P.eval(U.T(rev(rw), s), 1n+y))), U.syn(rev(rw), s, y)) : {P.eval(lsp(1n+d, Con{s, rw}), y) == _ : Nat}
          %rev_rev(U.T(rev(rw), s)) : {P.eval(lsp(1n+d, Con{s, rw}), y) == Nat.add(U.H(rev(rw), s), Nat.mul(y, P.eval(_, 1n+y))) : Nat}
          %ev_lsp(d, rev(U.T(rev(rw), s)), y, hlen(rw, s, d, hl)) : {P.eval(lsp(1n+d, Con{s, rw}), y) == Nat.add(U.H(rev(rw), s), Nat.mul(y, _)) : Nat}
          {==}

# Lengths survive the model
# -------------------------

def len_upd(l: List<&2, Nat>, +i: Nat, -v: Nat) -> {len(l) == len(A.upd(l, i, v)) : Nat}:
  match l:
    case Nil{}:
      {==}
    case Con{h, t}:
      match i:
        case 0n:
          {==}
        case 1n+p:
          %len_upd(t, p, v) : {1n+len(t) == 1n+_ : Nat}
          {==}

def len_LL(+k: Nat, +l: List<&2, Nat>, +s: Nat, +j: Nat) -> {len(l) == len(Pair.fst(List<&2, Nat>, Nat, LL(k, (l, s), j))) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n++q:
      %len_LL(q, A.upd(l, Nat.add(j, q), Nat.add(A.nth(l, Nat.add(j, q)), s)), Nat.add(A.nth(l, Nat.add(j, q)), s), j) : {len(l) == _ : Nat}
      len_upd(l, Nat.add(j, q), Nat.add(A.nth(l, Nat.add(j, q)), s))

def len_LP(+c: Nat, +l: List<&2, Nat>, +j: Nat) -> {len(l) == len(Pair.fst(List<&2, Nat>, Nat, LP(c, l, j))) : Nat}:
  len_LL(c, l, A.nth(l, Nat.add(j, c)), j)
