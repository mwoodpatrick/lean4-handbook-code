/- 第7章 方程式と不等式
   7.5 連立方程式・分数式 -/
import Mathlib

namespace Handbook.C07

-- BOOK: begin fs-basic
-- 分数式は field_simp で分母を払ってから ring/linarith へ
example (x : ℚ) (hx : x ≠ 0) : (x + 1) / x - 1 / x = 1 := by
  field_simp
  ring

example (a b : ℚ) (hb : b ≠ 0) : a / b * b = a := by
  field_simp
-- BOOK: end fs-basic

-- BOOK: begin fs-system
-- 連立1次方程式は linarith で解ける
example (x y : ℚ) (h1 : x + y = 5) (h2 : x - y = 1) :
    x = 3 ∧ y = 2 := by
  constructor <;> linarith
-- BOOK: end fs-system

-- BOOK: begin equations-exercises
-- 演習: 方程式1問・不等式2問
example (x : ℚ) : 2 * x - 7 = 3 ↔ x = 5 := by
  constructor
  · intro h; linarith
  · rintro rfl; norm_num

example (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

example (x : ℝ) (h : 0 < x) : 0 < x ^ 3 + x := by positivity
-- BOOK: end equations-exercises

end Handbook.C07
