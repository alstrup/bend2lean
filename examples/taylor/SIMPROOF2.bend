# SIMPROOF2: the template run on Base's Array tracks the list model step by
# step. Arrays are A.build(6n, l), the 64-slot perfect tree over a list, and
# ARRLAWS proves Array.get and Array.set on such trees: nothing is assumed,
# and everything is over Base. With LISTPROOF this proves the fast in-place
# shift (main.bend ashift) computes p(x+1).

import Base
import ./main.bend as P
import ./PROOF.bend as N
import ./LISTPROOF.bend as LT
import ./ARRLAWS.bend as A

def AL(k: Nat, r: Array<Nat> & Nat, +j: Nat) -> Array<Nat> & Nat:
  P.tloop(~Array<Nat>, ~(a => i => P.arr_get(a, i)), ~(a => i => v => P.arr_set(a, i, v)), k, r, j)

def AP(+c: Nat, a: Array<Nat>, +j: Nat) -> Array<Nat> & Nat:
  P.tpass(~Array<Nat>, ~(a => i => P.arr_get(a, i)), ~(a => i => v => P.arr_set(a, i, v)), c, a, j)

# from_nat and to_nat
# -------------------

def lt_le_trans(+a: Nat, +b: Nat, +c: Nat, +h1: A.lt(a, b), +h2: A.le(b, c)) -> A.lt(a, c):
  match a:
    case 0n:
      match b:
        case 0n:
          A.efq(A.lt(0n, c), A.ft(h1))
        case 1n+q:
          match c:
            case 0n:
              A.efq(A.lt(0n, 0n), A.ft(h2))
            case 1n+r:
              {==}
    case 1n++p:
      match b:
        case 0n:
          A.efq(A.lt(1n+p, c), A.ft(h1))
        case 1n++q:
          match c:
            case 0n:
              A.efq(A.lt(1n+p, 0n), A.ft(h2))
            case 1n++r:
              lt_le_trans(p, q, r, h1, h2)

def le_refl(+n: Nat) -> A.le(n, n):
  match n:
    case 0n:
      {==}
    case 1n++p:
      le_refl(p)

# 2^e <= 2^(e+k), without computing either.
def pow_le(+e: Nat, +k: Nat) -> A.le(Nat.pow(2n, e), Nat.pow(2n, Nat.add(e, k))):
  match k:
    case 0n:
      %N.add_zero(e) : A.le(Nat.pow(2n, e), Nat.pow(2n, _))
      le_refl(Nat.pow(2n, e))
    case 1n++m:
      %N.add_succ(e, m) : A.le(Nat.pow(2n, e), Nat.pow(2n, _))
      %A.tps(Nat.add(e, m)) : A.le(Nat.pow(2n, e), _)
      A.le_trans(Nat.pow(2n, e), Nat.pow(2n, Nat.add(e, m)), Nat.double(Nat.pow(2n, Nat.add(e, m))), pow_le(e, m), A.le_double(Nat.pow(2n, Nat.add(e, m))))

def inc_val.e(+x: Nat, +q: Nat, +m: Nat, +e: {q == m : Nat}, +h: A.lt(x, m)) -> A.lt(x, q):
  %Equal.sym(Nat, q, m, e) : A.lt(x, _)
  h

# Incrementing a word below its top adds one; the top is m, never computed.
def inc_val(+n: Nat, w: Word(n), +m: Nat, +e: {Nat.pow(2n, n) == m : Nat}, +h: A.lt(1n+Word.to_nat(n, w), m)) -> {1n+Word.to_nat(n, w) == Word.to_nat(n, Word.inc(n, w)) : Nat}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          A.efq({1n == 0n : Nat}, A.ft(inc_val.e(1n, Nat.pow(2n, 0n), m, e, h)))
    case 1n++p:
      match w:
        case WCon{False{}, +t}:
          {==}
        case WCon{True{}, +t}:
          +h1 = inc_val.e(2n+Nat.double(Word.to_nat(p, t)), Nat.pow(2n, 1n+p), m, e, h)
          +h2 = A.lt_dd(1n+Word.to_nat(p, t), Nat.pow(2n, p), A.lt_p2s(2n+Nat.double(Word.to_nat(p, t)), p, h1))
          %inc_val(p, t, Nat.pow(2n, p), {==}, h2) : {2n+Nat.double(Word.to_nat(p, t)) == Nat.double(_) : Nat}
          {==}

def inc_u32(u: U32, +m: Nat, +e: {Nat.pow(2n, 32n) == m : Nat}, +h: A.lt(1n+U32.to_nat(u), m)) -> {1n+U32.to_nat(u) == U32.to_nat(U32.inc(u)) : Nat}:
  match u:
    case U32{+w}:
      inc_val(32n, w, m, e, h)

def tfn.h(+p: Nat, +m: Nat, +h: A.lt(1n+p, m), +ih: {p == U32.to_nat(U32.from_nat(p)) : Nat}) -> A.lt(1n+U32.to_nat(U32.from_nat(p)), m):
  %ih : A.lt(1n+_, m)
  h

# Converting a natural below m = 2^32 to U32 and back is the identity.
def tfn.m(+m: Nat, +e: {Nat.pow(2n, 32n) == m : Nat}, +i: Nat, +h: A.lt(i, m)) -> {i == U32.to_nat(U32.from_nat(i)) : Nat}:
  match i:
    case 0n:
      {==}
    case 1n++p:
      +ih = tfn.m(m, e, p, A.lt_pred(p, m, h))
      %inc_u32(U32.from_nat(p), m, e, tfn.h(p, m, h, ih)) : {1n+p == _ : Nat}
      %ih : {1n+p == 1n+_ : Nat}
      {==}

def tfn(+i: Nat, +h: A.lt(i, Nat.pow(2n, 32n))) -> {i == U32.to_nat(U32.from_nat(i)) : Nat}:
  tfn.m(Nat.pow(2n, 32n), {==}, i, h)

# Bounds
# ------


def hbq(+j: Nat, +q: Nat, +r: Nat, +hb: {Nat.add(Nat.add(j, 1n+q), r) == 63n : Nat}) -> {Nat.add(Nat.add(j, q), 1n+r) == 63n : Nat}:
  %N.add_succ(Nat.add(j, q), r) : {_ == 63n : Nat}
  %Equal.sym(Nat, 1n+Nat.add(j, q), Nat.add(j, 1n+q), N.add_succ(j, q)) : {Nat.add(_, r) == 63n : Nat}
  hb

def hbs(+j: Nat, +d: Nat, +r: Nat, +hb: {Nat.add(Nat.add(j, 1n+d), r) == 63n : Nat}) -> {Nat.add(Nat.add(1n+j, d), r) == 63n : Nat}:
  %Equal.sym(Nat, 1n+Nat.add(j, d), Nat.add(j, 1n+d), N.add_succ(j, d)) : {Nat.add(_, r) == 63n : Nat}
  hb

def lt64.s(+i: Nat, +m: Nat, +h: A.le(i, m)) -> A.lt(i, 1n+m):
  match i:
    case 0n:
      {==}
    case 1n++p:
      match m:
        case 0n:
          A.efq(A.lt(1n+p, 1n), A.ft(h))
        case 1n++n:
          lt64.s(p, n, h)


def lt64.go(+i: Nat, +m: Nat, +r: Nat, +hm: {m == 63n : Nat}, +h: A.le(i, m)) -> A.lt(i, Nat.pow(2n, 6n)):
  %hm : A.lt(i, 1n+_)
  lt64.s(i, m, h)


def lt64(+i: Nat, +r: Nat, +hb: {Nat.add(i, r) == 63n : Nat}) -> A.lt(i, Nat.pow(2n, 6n)):
  lt64.go(i, Nat.add(i, r), r, hb, A.le_add_right(i, r))

def lt32(+i: Nat, +r: Nat, +hb: {Nat.add(i, r) == 63n : Nat}) -> A.lt(i, Nat.pow(2n, 32n)):
  lt_le_trans(i, Nat.pow(2n, 6n), Nat.pow(2n, 32n), lt64(i, r, hb), pow_le(6n, 26n))

# reading and writing slot i of build(6n, l), slots named by Nat
def hix(+i: Nat, +r: Nat, +hb: {Nat.add(i, r) == 63n : Nat}) -> A.lt(U32.to_nat(U32.from_nat(i)), Nat.pow(2n, 6n)):
  %tfn(i, lt32(i, r, hb)) : A.lt(_, Nat.pow(2n, 6n))
  lt64(i, r, hb)

def rd(+l: List<&2, Nat>, +i: Nat, +r: Nat, +hb: {Nat.add(i, r) == 63n : Nat}) -> {(A.build(6n, l), A.nth(l, i)) == P.arr_get(A.build(6n, l), i) : Array<Nat> & Nat}:
  %Equal.sym(Nat, i, U32.to_nat(U32.from_nat(i)), tfn(i, lt32(i, r, hb))) : {(A.build(6n, l), A.nth(l, _)) == P.arr_get(A.build(6n, l), i) : Array<Nat> & Nat}
  A.get_r(6n, l, U32.from_nat(i), {==}, hix(i, r, hb))

def wr(+l: List<&2, Nat>, +i: Nat, +v: Nat, +r: Nat, +hb: {Nat.add(i, r) == 63n : Nat}, +hl: A.le(Nat.pow(2n, 6n), A.len(l))) -> {A.build(6n, A.upd(l, i, v)) == P.arr_set(A.build(6n, l), i, v) : Array<Nat>}:
  %Equal.sym(Nat, i, U32.to_nat(U32.from_nat(i)), tfn(i, lt32(i, r, hb))) : {A.build(6n, A.upd(l, _, v)) == P.arr_set(A.build(6n, l), i, v) : Array<Nat>}
  A.set_r(6n, l, U32.from_nat(i), v, {==}, hix(i, r, hb), hl)

def len_eq(l: List<&2, Nat>) -> {LT.len(l) == A.len(l) : Nat}:
  match l:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %len_eq(t) : {1n+LT.len(t) == 1n+_ : Nat}
      {==}

def hl_upd(+l: List<&2, Nat>, +i: Nat, +v: Nat, +hl: A.le(Nat.pow(2n, 6n), A.len(l))) -> A.le(Nat.pow(2n, 6n), A.len(A.upd(l, i, v))):
  %len_eq(A.upd(l, i, v)) : A.le(Nat.pow(2n, 6n), _)
  %LT.len_upd(l, i, v) : A.le(Nat.pow(2n, 6n), _)
  %Equal.sym(Nat, LT.len(l), A.len(l), len_eq(l)) : A.le(Nat.pow(2n, 6n), _)
  hl

def hl_LP(+c: Nat, +l: List<&2, Nat>, +j: Nat, +hl: A.le(Nat.pow(2n, 6n), A.len(l))) -> A.le(Nat.pow(2n, 6n), A.len(Pair.fst(List<&2, Nat>, Nat, LT.LP(c, l, j)))):
  %len_eq(Pair.fst(List<&2, Nat>, Nat, LT.LP(c, l, j))) : A.le(Nat.pow(2n, 6n), _)
  %LT.len_LP(c, l, j) : A.le(Nat.pow(2n, 6n), _)
  %Equal.sym(Nat, LT.len(l), A.len(l), len_eq(l)) : A.le(Nat.pow(2n, 6n), _)
  hl

# Simulation
# ----------

def sim_loop(+k: Nat, -a: Array<Nat>, +l: List<&2, Nat>, +s: Nat, +j: Nat, +r: Nat, +hA: {A.build(6n, l) == a : Array<Nat>}, +hl: A.le(Nat.pow(2n, 6n), A.len(l)), +hb: {Nat.add(Nat.add(j, k), r) == 63n : Nat}) -> {(A.build(6n, Pair.fst(List<&2, Nat>, Nat, LT.LL(k, (l, s), j))), Pair.snd(List<&2, Nat>, Nat, LT.LL(k, (l, s), j))) == AL(k, (a, s), j) : Array<Nat> & Nat}:
  match k:
    case 0n:
      %hA : {(A.build(6n, l), s) == (_, s) : Array<Nat> & Nat}
      {==}
    case 1n++q:
      +hb1 = hbq(j, q, r, hb)
      %hA : {(A.build(6n, Pair.fst(List<&2, Nat>, Nat, LT.LL(1n+q, (l, s), j))), Pair.snd(List<&2, Nat>, Nat, LT.LL(1n+q, (l, s), j))) == AL(q, P.tstep.k(~Array<Nat>, ~(a => i => v => P.arr_set(a, i, v)), Nat.add(j, q), s, P.arr_get(_, Nat.add(j, q))), j) : Array<Nat> & Nat}
      %rd(l, Nat.add(j, q), 1n+r, hb1) : {(A.build(6n, Pair.fst(List<&2, Nat>, Nat, LT.LL(1n+q, (l, s), j))), Pair.snd(List<&2, Nat>, Nat, LT.LL(1n+q, (l, s), j))) == AL(q, P.tstep.k(~Array<Nat>, ~(a => i => v => P.arr_set(a, i, v)), Nat.add(j, q), s, _), j) : Array<Nat> & Nat}
      sim_loop(q, P.arr_set(A.build(6n, l), Nat.add(j, q), Nat.add(A.nth(l, Nat.add(j, q)), s)), A.upd(l, Nat.add(j, q), Nat.add(A.nth(l, Nat.add(j, q)), s)), Nat.add(A.nth(l, Nat.add(j, q)), s), j, 1n+r, wr(l, Nat.add(j, q), Nat.add(A.nth(l, Nat.add(j, q)), s), 1n+r, hb1, hl), hl_upd(l, Nat.add(j, q), Nat.add(A.nth(l, Nat.add(j, q)), s), hl), hb1)

def sim_pass(+c: Nat, -a: Array<Nat>, +l: List<&2, Nat>, +j: Nat, +r: Nat, +hA: {A.build(6n, l) == a : Array<Nat>}, +hl: A.le(Nat.pow(2n, 6n), A.len(l)), +hb: {Nat.add(Nat.add(j, c), r) == 63n : Nat}) -> {(A.build(6n, Pair.fst(List<&2, Nat>, Nat, LT.LP(c, l, j))), Pair.snd(List<&2, Nat>, Nat, LT.LP(c, l, j))) == AP(c, a, j) : Array<Nat> & Nat}:
  %hA : {(A.build(6n, Pair.fst(List<&2, Nat>, Nat, LT.LP(c, l, j))), Pair.snd(List<&2, Nat>, Nat, LT.LP(c, l, j))) == AL(c, P.arr_get(_, Nat.add(j, c)), j) : Array<Nat> & Nat}
  %rd(l, Nat.add(j, c), r, hb) : {(A.build(6n, Pair.fst(List<&2, Nat>, Nat, LT.LP(c, l, j))), Pair.snd(List<&2, Nat>, Nat, LT.LP(c, l, j))) == AL(c, _, j) : Array<Nat> & Nat}
  sim_loop(c, A.build(6n, l), l, A.nth(l, Nat.add(j, c)), j, r, {==}, hl, hb)

def sim_shift(+c: Nat, -a: Array<Nat>, +l: List<&2, Nat>, +j: Nat, +r: Nat, +hA: {A.build(6n, l) == a : Array<Nat>}, +hl: A.le(Nat.pow(2n, 6n), A.len(l)), +hb: {Nat.add(Nat.add(j, c), r) == 63n : Nat}) -> {A.build(6n, LT.TSH(c, l, j)) == P.ashift(c, a, j) : Array<Nat>}:
  match c:
    case 0n:
      hA
    case 1n++d:
      +e1 = sim_pass(1n+d, a, l, j, r, hA, hl, hb)
      +hA2 = Equal.cong(Array<Nat> & Nat, Array<Nat>, p => Pair.fst(Array<Nat>, Nat, p), (A.build(6n, Pair.fst(List<&2, Nat>, Nat, LT.LP(1n+d, l, j))), Pair.snd(List<&2, Nat>, Nat, LT.LP(1n+d, l, j))), AP(1n+d, a, j), e1)
      sim_shift(d, Pair.fst(Array<Nat>, Nat, AP(1n+d, a, j)), Pair.fst(List<&2, Nat>, Nat, LT.LP(1n+d, l, j)), 1n+j, r, hA2, hl_LP(1n+d, l, j, hl), hbs(j, d, r, hb))

# The theorem: on the 64-slot tree over pre ++ rev(R) ++ rest (at least 64 entries), with the region rev(R) of 1+c slots below slot 64, ashift leaves the tree over pre ++ lsp(c, R) ++ rest; LT.ev_lsp gives lsp(c, R) at y = rev(R) at y+1.
def ashift_ok(+c: Nat, -a: Array<Nat>, +pre: List<&2, Nat>, +R: List<&2, Nat>, +rest: List<&2, Nat>, +r: Nat, +hA: {A.build(6n, LT.app(pre, LT.app(LT.rev(R), rest))) == a : Array<Nat>}, +hl: A.le(Nat.pow(2n, 6n), A.len(LT.app(pre, LT.app(LT.rev(R), rest)))), +hR: {LT.len(R) == 1n+c : Nat}, +hb: {Nat.add(Nat.add(LT.len(pre), c), r) == 63n : Nat}) -> {A.build(6n, LT.app(pre, LT.app(LT.lsp(c, R), rest))) == P.ashift(c, a, LT.len(pre)) : Array<Nat>}:
  Equal.trans(Array<Nat>, A.build(6n, LT.app(pre, LT.app(LT.lsp(c, R), rest))), A.build(6n, LT.TSH(c, LT.app(pre, LT.app(LT.rev(R), rest)), LT.len(pre))), P.ashift(c, a, LT.len(pre)), Equal.cong(List<&2, Nat>, Array<Nat>, x => A.build(6n, x), LT.app(pre, LT.app(LT.lsp(c, R), rest)), LT.TSH(c, LT.app(pre, LT.app(LT.rev(R), rest)), LT.len(pre)), LT.shift_r(c, pre, R, rest, hR)), sim_shift(c, a, LT.app(pre, LT.app(LT.rev(R), rest)), LT.len(pre), r, hA, hl, hb))
