/- 第35章 数論
   35.3 Pell 方程式 -/
import Mathlib

namespace Handbook.C35

-- BOOK: begin pell-exists
-- Pell 方程式 x² - d y² = 1 は d が平方数でなければ自明でない解を持つ
example (d : ℤ) (hd : 0 < d) (hsq : ¬IsSquare d) :
    ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = 1 ∧ y ≠ 0 :=
  Pell.exists_of_not_isSquare hd hsq
-- BOOK: end pell-exists

-- BOOK: begin pell-examples
-- d = 2 の基本解 (3, 2)、d = 3 の基本解 (2, 1)
example : (3 : ℤ) ^ 2 - 2 * 2 ^ 2 = 1 := by norm_num
example : (2 : ℤ) ^ 2 - 3 * 1 ^ 2 = 1 := by norm_num

-- 基本解から次の解が作れる: (3+2√2)² = 17 + 12√2
example : (17 : ℤ) ^ 2 - 2 * 12 ^ 2 = 1 := by norm_num

-- d = 4 は平方数なので自明解しかない
example (y : ℤ) (h : (1 : ℤ) ^ 2 - 4 * y ^ 2 = 1) : y = 0 := by
  have : (4 : ℤ) * y ^ 2 = 0 := by linarith
  have : y ^ 2 = 0 := by linarith
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
-- BOOK: end pell-examples

end Handbook.C35
