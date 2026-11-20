# poly: the proofs. No tactics: every ring step is a named rewrite.

import Base
import ./main.bend as P
import ./LAWS.bend as Laws

# Nat ring lemmas (Base proves none of these)
# ----------------------------------------

def add_zero(a: Nat) -> {a == Nat.add(a, 0n) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+p == 1n+_ : Nat}
      {==}

def add_succ(a: Nat, -b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {2n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      %add_zero(b) : {b == _ : Nat}
      {==}
    case 1n+p:
      %add_succ(b, p) : {1n+Nat.add(p, b) == _ : Nat}
      %add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, b), c) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, b, c) : {1n+Nat.add(p, Nat.add(b, c)) == 1n+_ : Nat}
      {==}

def add_swap(x: Nat, +y: Nat, +z: Nat) -> {Nat.add(x, Nat.add(y, z)) == Nat.add(y, Nat.add(x, z)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+q:
      %add_succ(y, Nat.add(q, z)) : {1n+Nat.add(q, Nat.add(y, z)) == _ : Nat}
      %add_swap(q, y, z) : {1n+Nat.add(q, Nat.add(y, z)) == 1n+_ : Nat}
      {==}

# (a+b)+(c+d) == (a+c)+(b+d), so a rewrite turns its right side into its left
def interchange(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  %add_assoc(a, c, Nat.add(b, d)) : {Nat.add(Nat.add(a, b), Nat.add(c, d)) == _ : Nat}
  %add_swap(b, c, d) : {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(a, _) : Nat}
  %add_assoc(a, b, Nat.add(c, d)) : {_ == Nat.add(a, Nat.add(b, Nat.add(c, d))) : Nat}
  {==}

def mul_ldist(+x: Nat, +a: Nat, +b: Nat) -> {Nat.mul(x, Nat.add(a, b)) == Nat.add(Nat.mul(x, a), Nat.mul(x, b)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n++p:
      %interchange(a, b, Nat.mul(p, a), Nat.mul(p, b)) : {Nat.add(Nat.add(a, b), Nat.mul(p, Nat.add(a, b))) == _ : Nat}
      %mul_ldist(p, a, b) : {Nat.add(Nat.add(a, b), Nat.mul(p, Nat.add(a, b))) == Nat.add(Nat.add(a, b), _) : Nat}
      {==}

def eval_add_go(p: List<&2, Nat>, q: List<&2, Nat>, +x: Nat) -> {P.eval(P.add(p, q), x) == Nat.add(P.eval(p, x), P.eval(q, x)) : Nat}:
  match p q:
    case Nil{} _:
      {==}
    case Con{+a, +ps} Nil{}:
      add_zero(P.eval(Con{a, ps}, x))
    case Con{+a, +ps} Con{+b, +qs}:
      %interchange(a, b, Nat.mul(x, P.eval(ps, x)), Nat.mul(x, P.eval(qs, x))) : {Nat.add(Nat.add(a, b), Nat.mul(x, P.eval(P.add(ps, qs), x))) == _ : Nat}
      %mul_ldist(x, P.eval(ps, x), P.eval(qs, x)) : {Nat.add(Nat.add(a, b), Nat.mul(x, P.eval(P.add(ps, qs), x))) == Nat.add(Nat.add(a, b), _) : Nat}
      %eval_add_go(ps, qs, x) : {Nat.add(Nat.add(a, b), Nat.mul(x, P.eval(P.add(ps, qs), x))) == Nat.add(Nat.add(a, b), Nat.mul(x, _)) : Nat}
      {==}

def Laws.eval_add(p, q, x):
  eval_add_go(p, q, x)

# Multiplication lemmas
# ---------------------

def mul_zero(a: Nat) -> {Nat.mul(a, 0n) == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      mul_zero(p)

def mul_succ(+a: Nat, +b: Nat) -> {Nat.add(a, Nat.mul(a, b)) == Nat.mul(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      %mul_succ(p, b) : {1n+Nat.add(p, Nat.add(b, Nat.mul(p, b))) == 1n+Nat.add(b, _) : Nat}
      %add_swap(p, b, Nat.mul(p, b)) : {1n+Nat.add(p, Nat.add(b, Nat.mul(p, b))) == 1n+_ : Nat}
      {==}

def mul_comm(+a: Nat, +b: Nat) -> {Nat.mul(a, b) == Nat.mul(b, a) : Nat}:
  match a:
    case 0n:
      %mul_zero(b) : {_ == Nat.mul(b, 0n) : Nat}
      {==}
    case 1n++p:
      %mul_succ(b, p) : {Nat.add(b, Nat.mul(p, b)) == _ : Nat}
      %mul_comm(p, b) : {Nat.add(b, Nat.mul(p, b)) == Nat.add(b, _) : Nat}
      {==}

# (a+b)*c == a*c + b*c, so a rewrite turns its right side into its left
def mul_dist(a: Nat, -b: Nat, +c: Nat) -> {Nat.add(Nat.mul(a, c), Nat.mul(b, c)) == Nat.mul(Nat.add(a, b), c) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %mul_dist(p, b, c) : {Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)) == Nat.add(c, _) : Nat}
      %add_assoc(c, Nat.mul(p, c), Nat.mul(b, c)) : {_ == Nat.add(c, Nat.add(Nat.mul(p, c), Nat.mul(b, c))) : Nat}
      {==}

def mul_assoc(+a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(a, Nat.mul(b, c)) == Nat.mul(Nat.mul(a, b), c) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      %mul_dist(b, Nat.mul(p, b), c) : {Nat.add(Nat.mul(b, c), Nat.mul(p, Nat.mul(b, c))) == _ : Nat}
      %mul_assoc(p, b, c) : {Nat.add(Nat.mul(b, c), Nat.mul(p, Nat.mul(b, c))) == Nat.add(Nat.mul(b, c), _) : Nat}
      {==}

# b*(a*c) == a*(b*c)
def mul_swap(+a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(b, Nat.mul(a, c)) == Nat.mul(a, Nat.mul(b, c)) : Nat}:
  %mul_comm(Nat.mul(a, c), b) : {_ == Nat.mul(a, Nat.mul(b, c)) : Nat}
  %mul_assoc(a, c, b) : {_ == Nat.mul(a, Nat.mul(b, c)) : Nat}
  %mul_comm(c, b) : {Nat.mul(a, Nat.mul(c, b)) == Nat.mul(a, _) : Nat}
  {==}

# x*a + x*b == x*(a+b): mul_ldist reversed, so a rewrite expands x*(a+b)
def mul_fold(+x: Nat, +a: Nat, +b: Nat) -> {Nat.add(Nat.mul(x, a), Nat.mul(x, b)) == Nat.mul(x, Nat.add(a, b)) : Nat}:
  Equal.sym(Nat, Nat.mul(x, Nat.add(a, b)), Nat.add(Nat.mul(x, a), Nat.mul(x, b)), mul_ldist(x, a, b))

# Evaluation laws
# ---------------

def eval_scale_go(+c: Nat, p: List<&2, Nat>, +x: Nat) -> {P.eval(P.scale(c, p), x) == Nat.mul(c, P.eval(p, x)) : Nat}:
  match p:
    case Nil{}:
      Equal.sym(Nat, Nat.mul(c, 0n), 0n, mul_zero(c))
    case Con{+a, +ps}:
      %mul_fold(c, a, Nat.mul(x, P.eval(ps, x))) : {Nat.add(Nat.mul(c, a), Nat.mul(x, P.eval(P.scale(c, ps), x))) == _ : Nat}
      %mul_swap(c, x, P.eval(ps, x)) : {Nat.add(Nat.mul(c, a), Nat.mul(x, P.eval(P.scale(c, ps), x))) == Nat.add(Nat.mul(c, a), _) : Nat}
      %eval_scale_go(c, ps, x) : {Nat.add(Nat.mul(c, a), Nat.mul(x, P.eval(P.scale(c, ps), x))) == Nat.add(Nat.mul(c, a), Nat.mul(x, _)) : Nat}
      {==}

def Laws.eval_scale(c, p, x):
  eval_scale_go(c, p, x)

def eval_mul_go(p: List<&2, Nat>, +q: List<&2, Nat>, +x: Nat) -> {P.eval(P.mul(p, q), x) == Nat.mul(P.eval(p, x), P.eval(q, x)) : Nat}:
  match p:
    case Nil{}:
      {==}
    case Con{+a, +ps}:
      %mul_dist(a, Nat.mul(x, P.eval(ps, x)), P.eval(q, x)) : {P.eval(P.mul(Con{a, ps}, q), x) == _ : Nat}
      %mul_assoc(x, P.eval(ps, x), P.eval(q, x)) : {P.eval(P.mul(Con{a, ps}, q), x) == Nat.add(Nat.mul(a, P.eval(q, x)), _) : Nat}
      %eval_mul_go(ps, q, x) : {P.eval(P.mul(Con{a, ps}, q), x) == Nat.add(Nat.mul(a, P.eval(q, x)), Nat.mul(x, _)) : Nat}
      %eval_scale_go(a, q, x) : {P.eval(P.mul(Con{a, ps}, q), x) == Nat.add(_, Nat.mul(x, P.eval(P.mul(ps, q), x))) : Nat}
      %eval_add_go(P.scale(a, q), Con{0n, P.mul(ps, q)}, x) : {P.eval(P.mul(Con{a, ps}, q), x) == _ : Nat}
      {==}

def Laws.eval_mul(p, q, x):
  eval_mul_go(p, q, x)

def eval_const(+a: Nat, +x: Nat) -> {P.eval(Con{a, Nil{}}, x) == a : Nat}:
  %Equal.sym(Nat, Nat.mul(x, 0n), 0n, mul_zero(x)) : {Nat.add(a, _) == a : Nat}
  %add_zero(a) : {_ == a : Nat}
  {==}

def eval_shift1_go(p: List<&2, Nat>, +x: Nat) -> {P.eval(P.shift1(p), x) == P.eval(p, 1n+x) : Nat}:
  match p:
    case Nil{}:
      {==}
    case Con{+a, +ps}:
      %eval_shift1_go(ps, x) : {P.eval(P.shift1(Con{a, ps}), x) == Nat.add(a, Nat.add(_, Nat.mul(x, _))) : Nat}
      %eval_add_go(P.shift1(ps), Con{0n, P.shift1(ps)}, x) : {P.eval(P.shift1(Con{a, ps}), x) == Nat.add(a, _) : Nat}
      %eval_const(a, x) : {P.eval(P.shift1(Con{a, ps}), x) == Nat.add(_, P.eval(P.add(P.shift1(ps), Con{0n, P.shift1(ps)}), x)) : Nat}
      %eval_add_go(Con{a, Nil{}}, P.add(P.shift1(ps), Con{0n, P.shift1(ps)}), x) : {P.eval(P.shift1(Con{a, ps}), x) == _ : Nat}
      {==}

def Laws.eval_shift1(p, x):
  eval_shift1_go(p, x)
