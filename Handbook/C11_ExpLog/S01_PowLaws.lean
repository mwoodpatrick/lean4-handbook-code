/- 第11章 指数関数と対数関数
   11.1 指数法則 -/
import Mathlib

namespace Handbook.C11

-- BOOK: begin pow-laws
-- 指数法則(自然数乗)
example (a : ℚ) (m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n :=
  pow_add a m n

example (a : ℚ) (m n : ℕ) : (a ^ m) ^ n = a ^ (m * n) :=
  (pow_mul a m n).symm
-- BOOK: end pow-laws

-- BOOK: begin pow-zpow
-- 整数乗(zpow): 負の指数は逆数を意味する
example (a : ℚ) : a ^ (-1 : ℤ) = a⁻¹ := zpow_neg_one a

example (a : ℚ) : a ^ (0 : ℤ) = 1 := zpow_zero a
-- BOOK: end pow-zpow

end Handbook.C11
