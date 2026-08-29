/- Chapter 12: Sequences and mathematical induction
   12.4 How induction works -- inductive types revisited -/
import Mathlib

namespace Handbook.C12

-- BOOK: begin ind-anatomy
-- The sum of the odd numbers is a square
theorem sum_odd (n : ℕ) :
    ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring
-- BOOK: end ind-anatomy

-- BOOK: begin nat-rec
-- The recursor of ℕ is the principle of induction itself
#check @Nat.rec
-- Nat.rec : {motive : ℕ → Sort u} → motive 0 →
--   (∀ n, motive n → motive (n + 1)) → ∀ n, motive n
-- BOOK: end nat-rec

-- BOOK: begin ind-two-step
-- A number-theoretic claim on the same skeleton
example (n : ℕ) : 2 ∣ n * (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨m + k + 1, ?_⟩
    have h : (k + 1) * (k + 1 + 1) = k * (k + 1) + 2 * (k + 1) := by
      ring
    rw [h, hm]
    ring

-- omega decides linear arithmetic over ℕ and ℤ
example (n : ℕ) (h : 2 * n + 1 = 7) : n = 3 := by omega
-- BOOK: end ind-two-step

end Handbook.C12
