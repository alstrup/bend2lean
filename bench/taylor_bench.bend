# bench_arr: bench.bend's workload with an in-place Taylor shift on an
# array (for i in 0..n-1, for j = n-1 down to i: a[j] += a[j+1]).
# Same coefficients at the same positions, so the same answer.

import Base
import ../examples/taylor/main.bend as P

def coef(+seed: Nat, +p: Nat) -> Nat:
  Nat.mod(Nat.add(Nat.mul(seed, 7919n), Nat.mul(p, 104729n)), 1000n)

# writes coef(seed, k-1), coef(seed, k-2), ... at i, i+1, ...
def fill(k: Nat, a: Array<Nat>, +seed: Nat, +i: U32) -> Array<Nat>:
  match k:
    case 0n:
      a
    case 1n++p:
      b = Array.set(Nat, a, i, coef(seed, p))
      fill(p, b, seed, (i + 1 : U32))

# one step: a[j] += a[j+1]. A pair a call returns is split by a def that
# takes it as a parameter (a match may not scrutinize a computed value).
def step.c(+j: U32, x: Nat, r: Array<Nat> & Nat) -> Array<Nat>:
  (c, y) = r
  Array.set(Nat, c, j, Nat.add(x, y))

def step.b(+j: U32, r: Array<Nat> & Nat) -> Array<Nat>:
  (b, x) = r
  step.c(j, x, Array.get(Nat, b, (j + 1 : U32)))

def step(a: Array<Nat>, +j: U32) -> Array<Nat>:
  step.b(j, Array.get(Nat, a, j))

# k steps, j counting down
def inner(k: Nat, a: Array<Nat>, +j: U32) -> Array<Nat>:
  match k:
    case 0n:
      a
    case 1n+p:
      inner(p, step(a, j), (j - 1 : U32))

# r = n, n-1, ..., 1 passes, each from j = n-1
def outer(r: Nat, a: Array<Nat>, +n1: U32) -> Array<Nat>:
  match r:
    case 0n:
      a
    case 1n++p:
      b = inner(1n+p, a, n1)
      outer(p, b, n1)

def take.b(acc: Nat, r: Array<Nat> & Nat) -> Array<Nat> & Nat:
  (b, x) = r
  (b, Nat.add(acc, x))

def take(st: Array<Nat> & Nat, +i: U32) -> Array<Nat> & Nat:
  (a, acc) = st
  take.b(acc, Array.get(Nat, a, i))

# the sum of k slots from i, carried beside the array
def sum(k: Nat, st: Array<Nat> & Nat, +i: U32) -> Nat:
  match k:
    case 0n:
      (a, acc) = st
      acc
    case 1n+p:
      sum(p, take(st, i), (i + 1 : U32))

# 36 coefficients (degree 35) in a 64-slot array; eval at 1 is the sum
def work(+seed: Nat) -> Nat:
  a = fill(36n, Array.new(Nat, 6n, 0n), seed, 0)
  Nat.mod(sum(36n, (P.ashift(35n, a, 0n), 0n), 0), 1000003n)

def go(depth: Nat, +lo: Nat) -> Nat:
  match depth:
    case 0n:
      work(lo)
    case 1n++p:
      a b = go(p, lo) go(p, Nat.add(lo, Nat.pow(2n, p)))
      Nat.mod(Nat.add(a, b), 1000003n)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(Nat.show(go(20n, 0n)))
