/- English edition source: Handbook/C12_Induction/S09_Strengthen.lean. -/
import Mathlib

namespace Handbook.C12

-- BOOK: begin str-target
-- The target: the sum of the odd numbers is a square,
-- 1+3+5+…+(2n-1) = n²
example (n : ℕ) :
    ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring
-- BOOK: end str-target

-- BOOK: begin str-weak
-- The strengthened form. An equation is easier to run induction on.
-- Trying to show only the ≤ side leaves the hypothesis too weak.
example (n : ℕ) :
    ∑ i ∈ Finset.range n, (2 * i + 1) ≤ n ^ 2 := by
  -- Go through an equality; left as an inequality, the IH is too weak
  -- to proceed
  have h : ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  omega
-- BOOK: end str-weak

-- BOOK: begin str-general
-- The typical case of generalizing in order to strengthen.
-- To show a n = 2^n - 1, follow the shape of the recurrence directly
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * a n + 1

example (n : ℕ) : a n = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    simp only [a, ih]
    omega
-- BOOK: end str-general

end Handbook.C12
