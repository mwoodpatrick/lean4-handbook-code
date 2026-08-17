/- 第12章 数列と数学的帰納法
   12.6b 三項間漸化式を一般項に直す -/
import Mathlib

namespace Handbook.C12

-- BOOK: begin lin-def
-- a(n+2) = 3a(n+1) - 2a(n), a0 = 0, a1 = 1
def s : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 3 * s (n + 1) - 2 * s n
-- BOOK: end lin-def

-- BOOK: begin lin-closed
-- 特性方程式 x² = 3x - 2 の解 1, 2 から a(n) = 2^n - 1 が出る
example (n : ℕ) : s n = 2 ^ n - 1 := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih1 ih2 =>
    show 3 * s (n + 1) - 2 * s n = 2 ^ (n + 2) - 1
    rw [ih1, ih2]
    ring
-- BOOK: end lin-closed

-- BOOK: begin lin-char
-- 特性方程式の解であることの検算。r = 1 と r = 2
example : (1 : ℤ) ^ 2 = 3 * 1 - 2 := by norm_num

example : (2 : ℤ) ^ 2 = 3 * 2 - 2 := by norm_num
-- BOOK: end lin-char

end Handbook.C12
