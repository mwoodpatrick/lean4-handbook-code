/- Chapter 12: Sequences and mathematical induction
   12.7 Three-term recurrences and the characteristic equation -/
import Mathlib

namespace Handbook.C12

-- BOOK: begin lin-def
-- a 0 = 0, a 1 = 1, a (n+2) = 3 a (n+1) - 2 a n
def linRec : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 3 * linRec (n + 1) - 2 * linRec n

#eval (List.range 6).map linRec  -- output: [0, 1, 3, 7, 15, 31]
-- BOOK: end lin-def

-- BOOK: begin lin-char
-- The characteristic equation r^2 = 3r - 2 has the roots 1 and 2
example (r : ℝ) : r ^ 2 = 3 * r - 2 ↔ r = 1 ∨ r = 2 := by
  constructor
  · intro h
    have h2 : (r - 1) * (r - 2) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num
-- BOOK: end lin-char

-- BOOK: begin lin-closed
-- The general term is a n = 2^n - 1;
-- a two-step recurrence needs two bases
theorem linRec_eq (n : ℕ) : linRec n = 2 ^ n - 1 := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [linRec]
  | one => norm_num [linRec]
  | more n ih1 ih2 =>
    simp only [linRec]
    rw [ih1, ih2]
    ring
-- BOOK: end lin-closed

end Handbook.C12
