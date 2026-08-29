/- English edition source: Handbook/C06_Numbers/S06_Extension.lean. -/
import Mathlib

namespace Handbook.C06

-- BOOK: begin ext-nat-int
-- In ℕ, x + 2 = 1 has no solution. Extending to ℤ makes it solvable.
example : ¬ ∃ n : ℕ, n + 2 = 1 := by
  rintro ⟨n, hn⟩
  omega

example : ∃ n : ℤ, n + 2 = 1 := ⟨-1, by ring⟩
-- BOOK: end ext-nat-int

-- BOOK: begin ext-int-rat
-- In ℤ, 2x = 1 has no solution. Extending to ℚ makes it solvable.
example : ¬ ∃ n : ℤ, 2 * n = 1 := by
  rintro ⟨n, hn⟩
  omega

example : ∃ q : ℚ, 2 * q = 1 := ⟨1 / 2, by norm_num⟩
-- BOOK: end ext-int-rat

-- BOOK: begin ext-dense
-- ℚ is dense in ℝ: between any two real numbers lies a rational number.
example (x y : ℝ) (h : x < y) :
    ∃ q : ℚ, x < (q : ℝ) ∧ (q : ℝ) < y :=
  exists_rat_btwn h
-- BOOK: end ext-dense

-- BOOK: begin ext-gap
-- Even so, ℚ has gaps: x² = 2 has no rational solution.
example : ¬ ∃ q : ℚ, q ^ 2 = 2 := by
  rintro ⟨q, hq⟩
  have hnn : (0 : ℝ) ≤ ((|q| : ℚ) : ℝ) := by
    exact_mod_cast abs_nonneg q
  have hsq : ((|q| : ℚ) : ℝ) ^ 2 = 2 := by
    push_cast
    rw [sq_abs]
    exact_mod_cast hq
  have h2 : ((|q| : ℚ) : ℝ) = Real.sqrt 2 := by
    rw [← hsq, Real.sqrt_sq hnn]
  exact irrational_sqrt_two ⟨|q|, h2⟩
-- BOOK: end ext-gap

end Handbook.C06
