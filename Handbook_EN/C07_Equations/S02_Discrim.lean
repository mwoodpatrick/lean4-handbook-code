/- Chapter 7: Equations and inequalities
   7.3 The discriminant -/
import Mathlib

namespace Handbook.C07

-- BOOK: begin discrim-def
-- mathlib's discriminant is exactly b^2 - 4ac
example (a b c : ℝ) : discrim a b c = b ^ 2 - 4 * a * c := rfl
-- BOOK: end discrim-def

-- BOOK: begin complete-square
-- Completing the square: multiply by 4a and a square appears
example (a b c x : ℝ) :
    4 * a * (a * x ^ 2 + b * x + c)
      = (2 * a * x + b) ^ 2 - discrim a b c := by
  simp only [discrim]
  ring
-- BOOK: end complete-square

-- BOOK: begin discrim-iff
-- There is a solution exactly when the discriminant is a square
-- (mathlib writes the leading term as a * (x * x), so rewrite it first)
example (a b c x : ℝ) (ha : a ≠ 0) :
    a * x ^ 2 + b * x + c = 0
      ↔ discrim a b c = (2 * a * x + b) ^ 2 := by
  rw [show a * x ^ 2 = a * (x * x) by ring]
  exact quadratic_eq_zero_iff_discrim_eq_sq ha x
-- BOOK: end discrim-iff

-- BOOK: begin discrim-neg
-- D = 1 - 4 = -3 < 0, so x^2 + x + 1 = 0 has no real solution
example : ¬ ∃ x : ℝ, x ^ 2 + x + 1 = 0 := by
  rintro ⟨x, hx⟩
  -- 4(x^2 + x + 1) = (2x + 1)^2 + 3 ≥ 3 > 0
  nlinarith [sq_nonneg (2 * x + 1)]
-- BOOK: end discrim-neg

end Handbook.C07
