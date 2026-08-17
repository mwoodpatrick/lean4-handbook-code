/- 第41章 証明自動化
   41.3 決定手続き -/
import Mathlib

namespace Handbook.C41

-- BOOK: begin decide
-- decide: 有限の場合を総当たりする
example : (2 : ℤ) ^ 10 = 1024 := by decide
example : ∀ a b : ZMod 4, a ^ 2 + b ^ 2 ≠ 3 := by decide
example : Nat.Prime 97 := by decide
-- BOOK: end decide

-- BOOK: begin omega
-- omega: 線形整数演算の決定手続き。ℕ の切り捨て減法も扱う
example (n : ℕ) : n % 3 < 3 := by omega
example (a b : ℤ) (h : 2 * a + 3 * b = 7) (h2 : a = 2) : b = 1 := by
  omega
example (n : ℕ) (h : 0 < n) : n - 1 + 1 = n := by omega
-- BOOK: end omega

-- BOOK: begin norm-num
-- norm_num: 数値計算を正規形へ。decide より広く速い
example : (123 : ℝ) * 456 = 56088 := by norm_num
example : (7 : ℚ) / 2 > 3 := by norm_num
example : Nat.Prime 1000003 := by norm_num
-- BOOK: end norm-num

end Handbook.C41
