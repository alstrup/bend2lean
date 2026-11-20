# poly: the laws. Each operation commutes with evaluation at every x.

import Base
import ./main.bend as P

law eval_add:
  for  p: List<&2, Nat>
  for  q: List<&2, Nat>
  for +x: Nat
  {P.eval(P.add(p, q), x) == Nat.add(P.eval(p, x), P.eval(q, x)) : Nat}

law eval_scale:
  for +c: Nat
  for  p: List<&2, Nat>
  for +x: Nat
  {P.eval(P.scale(c, p), x) == Nat.mul(c, P.eval(p, x)) : Nat}

law eval_mul:
  for  p: List<&2, Nat>
  for +q: List<&2, Nat>
  for +x: Nat
  {P.eval(P.mul(p, q), x) == Nat.mul(P.eval(p, x), P.eval(q, x)) : Nat}

law eval_shift1:
  for  p: List<&2, Nat>
  for +x: Nat
  {P.eval(P.shift1(p), x) == P.eval(p, 1n+x) : Nat}
