/- 第7章 方程式と不等式
   7.2 判別式と実数解の存在 -/
import Mathlib

namespace Handbook.C07

-- BOOK: begin discrim-def
-- 判別式 b² - 4ac は mathlib では discrim
#check discrim  -- discrim a b c = b ^ 2 - 4 * a * c

example : discrim (1 : ℚ) (-5) 6 = 1 := by
  unfold discrim
  norm_num
-- BOOK: end discrim-def

-- BOOK: begin complete-square
-- 解の公式の心臓部: 平方完成の恒等式
example (a b c x : ℚ) (ha : a ≠ 0) :
    a * x ^ 2 + b * x + c
      = a * (x + b / (2 * a)) ^ 2 - discrim a b c / (4 * a) := by
  simp only [discrim]
  field_simp
  ring
-- BOOK: end complete-square

-- BOOK: begin discrim-iff
-- ax² + bx + c = 0 ⟺ 判別式が (2ax + b)² に等しい
example (a b c x : ℚ) (ha : a ≠ 0) :
    a * (x * x) + b * x + c = 0 ↔
      discrim a b c = (2 * a * x + b) ^ 2 :=
  quadratic_eq_zero_iff_discrim_eq_sq ha x
-- BOOK: end discrim-iff

-- BOOK: begin discrim-neg
-- D < 0 の実例: x² + x + 1 = 0 に実数解はない
-- 種明かし: 4(x² + x + 1) = (2x + 1)² + 3 > 0
example (x : ℝ) : x ^ 2 + x + 1 ≠ 0 := by
  nlinarith [sq_nonneg (2 * x + 1)]
-- BOOK: end discrim-neg

end Handbook.C07
