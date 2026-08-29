/- Chapter 35: Number theory
   35.4 Pell's equation -/
import Mathlib

namespace Handbook.C35

-- BOOK: begin pell-exists
-- Pell's equation x² - d y² = 1 has a non-trivial solution
-- whenever d is not a square
example (d : ℤ) (hd : 0 < d) (hsq : ¬IsSquare d) :
    ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = 1 ∧ y ≠ 0 :=
  Pell.exists_of_not_isSquare hd hsq
-- BOOK: end pell-exists

-- BOOK: begin pell-examples
-- The fundamental solution is (3, 2) for d = 2 and (2, 1) for d = 3
example : (3 : ℤ) ^ 2 - 2 * 2 ^ 2 = 1 := by norm_num
example : (2 : ℤ) ^ 2 - 3 * 1 ^ 2 = 1 := by norm_num

-- the next solution comes from the fundamental one:
-- (3+2√2)² = 17 + 12√2
example : (17 : ℤ) ^ 2 - 2 * 12 ^ 2 = 1 := by norm_num

-- d = 4 is a square, so only the trivial solution remains
example (y : ℤ) (h : (1 : ℤ) ^ 2 - 4 * y ^ 2 = 1) : y = 0 := by
  have h4 : (4 : ℤ) * y ^ 2 = 0 := by linarith
  have hy : y ^ 2 = 0 := by linarith
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hy
-- BOOK: end pell-examples

end Handbook.C35
