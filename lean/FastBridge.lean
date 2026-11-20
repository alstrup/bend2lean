-- The Lean-facing statement of Bend's proof that the fast in-place Taylor shift
-- (main.bend ashift, the template on Base's Array) computes p(x+1). Appended to the
-- bend2lean translation of SIMPROOF2.bend, whose proofs Lean's kernel re-checks.

namespace Bend

theorem lb_add_eq (a b : Nat) : «Nat.add» a b = a + b := by
  induction a with
  | zero => simp [«Nat.add»]
  | succ n ih => simp [«Nat.add», ih]; omega

theorem lb_mul_eq (a b : Nat) : «Nat.mul» a b = a * b := by
  induction a with
  | zero => simp [«Nat.mul»]
  | succ n ih => simp [«Nat.mul», ih, lb_add_eq, Nat.succ_mul]; omega

theorem lb_len_eq (xs : List Nat) : «LISTPROOF:len» xs = xs.length := by
  induction xs with
  | nil => simp [«LISTPROOF:len»]
  | cons x t ih => simp [«LISTPROOF:len», ih]

theorem lb_alen_eq (xs : List Nat) : «ARRLAWS:len» xs = xs.length := by
  induction xs with
  | nil => simp [«ARRLAWS:len»]
  | cons x t ih => simp [«ARRLAWS:len», ih]

theorem lb_app_eq (xs ys : List Nat) : «LISTPROOF:app» xs ys = xs ++ ys := by
  induction xs with
  | nil => simp [«LISTPROOF:app»]
  | cons x t ih => simp [«LISTPROOF:app», ih]

theorem lb_app1_eq (xs : List Nat) (s : Nat) : «PURE:app1» xs s = xs ++ [s] := by
  induction xs with
  | nil => simp [«PURE:app1»]
  | cons x t ih => simp [«PURE:app1», ih]

theorem lb_rev_eq (xs : List Nat) : «LISTPROOF:rev» xs = xs.reverse := by
  induction xs with
  | nil => simp [«LISTPROOF:rev»]
  | cons x t ih => simp [«LISTPROOF:rev», ih, lb_app1_eq]

theorem lb_is_le_eq (a b : Nat) : «Nat.is_le» a b = decide (a ≤ b) := by
  induction a generalizing b with
  | zero => cases b <;> rfl
  | succ n ih => cases b with
    | zero => rfl
    | succ m => simp only [«Nat.is_le», «Nat.cmp»] at *; rw [ih m]; simp

theorem lb_le_eq (a b : Nat) : «ARRLAWS:le» a b ↔ a ≤ b := by
  simp [«ARRLAWS:le», lb_is_le_eq]

/-- Horner evaluation of a coefficient list, lowest degree first. -/
def horner (p : List Nat) (y : Nat) : Nat := p.foldr (fun a acc => a + y * acc) 0

theorem lb_eval_eq (p : List Nat) (y : Nat) : «main:eval» p y = horner p y := by
  induction p with
  | nil => simp [«main:eval», horner]
  | cons a t ih => simp [«main:eval», horner, lb_add_eq, lb_mul_eq] at *; rw [ih]

/-- Bend's fast in-place Taylor shift on a 64-slot array. Take the array built from a
list `pre ++ R.reverse ++ rest` of at least 64 entries, with the region `R.reverse`
(c+1 coefficients, starting at `pre.length`) ending below slot 64. Then `ashift`
returns the array built from `pre ++ Q ++ rest`, where `Q` at `y` is the old region at
`y + 1`. Proved in Bend (SIMPROOF2.bend `ashift_ok`, LISTPROOF.bend `ev_lsp`, over
ARRLAWS's Array laws) and re-checked here by Lean's kernel. -/
theorem fast_taylor_shift (c : Nat) (pre R rest : List Nat) (hR : R.length = c + 1)
    (hlen : 64 ≤ (pre ++ (R.reverse ++ rest)).length) (hfit : pre.length + c ≤ 63) :
    ∃ Q : List Nat,
      «main:ashift» c («ARRLAWS:build» 6 (pre ++ (R.reverse ++ rest))) pre.length
        = «ARRLAWS:build» 6 (pre ++ (Q ++ rest)) ∧
      ∀ y, horner Q y = horner R.reverse (y + 1) := by
  refine ⟨«LISTPROOF:lsp» c R, ?_, ?_⟩
  · have hA : «ARRLAWS:build» 6 («LISTPROOF:app» pre («LISTPROOF:app» («LISTPROOF:rev» R) rest))
        = «ARRLAWS:build» 6 (pre ++ (R.reverse ++ rest)) := by simp [lb_app_eq, lb_rev_eq]
    have hl : «ARRLAWS:le» («Nat.pow» 2 6)
        («ARRLAWS:len» («LISTPROOF:app» pre («LISTPROOF:app» («LISTPROOF:rev» R) rest))) := by
      rw [lb_le_eq, lb_alen_eq, lb_app_eq, lb_app_eq, lb_rev_eq]
      have : «Nat.pow» 2 6 = 64 := rfl
      rw [this]; exact hlen
    have hR' : «LISTPROOF:len» R = Nat.succ c := by rw [lb_len_eq]; exact hR
    have hb : «Nat.add» («Nat.add» («LISTPROOF:len» pre) c) (63 - (pre.length + c)) = 63 := by
      rw [lb_add_eq, lb_add_eq, lb_len_eq]; omega
    have h := «ashift_ok» c _ pre R rest (63 - (pre.length + c)) hA hl hR' hb
    simp only [lb_app_eq, lb_len_eq] at h
    exact h.symm
  · intro y
    have hR' : «LISTPROOF:len» R = Nat.succ c := by rw [lb_len_eq]; exact hR
    have h := «LISTPROOF:ev_lsp» c R y hR'
    simp only [lb_eval_eq, lb_rev_eq] at h
    exact h

end Bend

#print axioms Bend.fast_taylor_shift
