-- bench_arr.bend in Lean: in-place Taylor shift on an Array Nat
-- (Lean mutates in place when the array is uniquely referenced).

def coef (seed p : Nat) : Nat := (seed * 7919 + p * 104729) % 1000

def shift (a : Array Nat) (n : Nat) : Array Nat := Id.run do
  let mut a := a
  for i in [0:n] do
    let mut j := n - 1
    for _ in [i:n] do
      a := a.set! j (a[j]! + a[j+1]!)
      j := j - 1
  return a

-- the same loops as tail recursion, mirroring bench_arr.bend
def inner : Nat → Array Nat → Nat → Array Nat
  | 0, a, _ => a
  | k + 1, a, j => inner k (a.set! j (a[j]! + a[j+1]!)) (j - 1)

def outer (n1 : Nat) : Nat → Array Nat → Array Nat
  | 0, a => a
  | r + 1, a => outer n1 r (inner (r + 1) a n1)

def work (seed : Nat) : Nat :=
  let a := (Array.range 36).map fun i => coef seed (35 - i)
  let b := if seed == 0xFFFFFFFFFF then shift a 35 else outer 34 35 a
  (b.foldl (· + ·) 0) % 1000003

def go : Nat → Nat → Nat
  | 0, lo => work lo
  | p + 1, lo => (go p lo + go p (lo + 2 ^ p)) % 1000003

def goPar (k depth : Nat) : Nat :=
  let chunk := depth - k
  let tasks := (List.range (2 ^ k)).map fun i => Task.spawn fun _ => go chunk (i * 2 ^ chunk)
  tasks.foldl (fun acc t => (acc + t.get) % 1000003) 0

def main (args : List String) : IO Unit := do
  let k := (args.head? >>= String.toNat?).getD 0
  let d := (args.tail.head? >>= String.toNat?).getD 20
  IO.println (if k == 0 then go d 0 else goPar k d)
