/- English edition source: Handbook/C06_Numbers/S04_Abs.lean. -/
import Mathlib

namespace Handbook.C06

-- BOOK: begin abs-basic
#eval |(-5 : ℤ)|  -- output: 5

example (x : ℚ) : 0 ≤ |x| := abs_nonneg x

-- The triangle inequality. All of analysis begins here.
example (x y : ℚ) : |x + y| ≤ |x| + |y| := abs_add_le x y
-- BOOK: end abs-basic

-- BOOK: begin abs-cases
-- Split cases exactly as in the definition: unchanged if nonnegative,
-- negate if negative
example (x : ℚ) (h : 0 ≤ x) : |x| = x := abs_of_nonneg h

example (x : ℚ) (h : x < 0) : |x| = -x := abs_of_neg h
-- BOOK: end abs-cases

-- BOOK: begin abs-lt
-- |x| < c is equivalent to -c < x < c
example (x : ℚ) (h : |x| < 1) : -1 < x ∧ x < 1 := abs_lt.mp h

example (x : ℚ) (h1 : -2 < x) (h2 : x < 2) : |x| < 2 :=
  abs_lt.mpr ⟨h1, h2⟩
-- BOOK: end abs-lt

-- BOOK: begin abs-sqrt
-- √(a²) = |a|. "Square and take the root" does not restore the
-- original; it erases the sign.
example (a : ℝ) : Real.sqrt (a ^ 2) = |a| :=
  Real.sqrt_sq_eq_abs a
-- BOOK: end abs-sqrt

-- BOOK: begin abs-eq
-- "Solve" an absolute-value equation: |x − 3| = 5 ⟺ x = 8 ∨ x = −2
example (x : ℚ) : |x - 3| = 5 ↔ x = 8 ∨ x = -2 := by
  rw [abs_eq (by norm_num : (0 : ℚ) ≤ 5)]
  constructor
  · rintro (h | h)
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num
-- BOOK: end abs-eq

-- BOOK: begin abs-rev-triangle
-- Example: the reverse triangle inequality, derived from a single use
-- of the triangle inequality.
example (a b : ℚ) : |a| - |b| ≤ |a - b| := by
  have h := abs_add_le (a - b) b
  have e : a - b + b = a := by ring
  rw [e] at h
  linarith

-- mathlib provides the general form
example (a b : ℚ) : |a| - |b| ≤ |a - b| :=
  abs_sub_abs_le_abs_sub a b
-- BOOK: end abs-rev-triangle

end Handbook.C06
