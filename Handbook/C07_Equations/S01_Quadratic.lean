/- 第7章 方程式と不等式
   7.1 1次・2次方程式と解の公式 -/
import Mathlib

namespace Handbook.C07

-- BOOK: begin quad-factor
-- x² - 5x + 6 = 0 の解は 2 と 3(因数分解による完全な証明)
example (x : ℚ) : x ^ 2 - 5 * x + 6 = 0 ↔ x = 2 ∨ x = 3 := by
  constructor
  · intro h
    have h2 : (x - 2) * (x - 3) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h' | h'
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num
-- BOOK: end quad-factor

-- BOOK: begin quad-linear
-- 1次方程式を「解く」= 解集合との同値を示す
example (x : ℚ) : 3 * x + 5 = 11 ↔ x = 2 := by
  constructor
  · intro h; linarith
  · rintro rfl; norm_num
-- BOOK: end quad-linear

-- BOOK: begin word-problem
-- 文章題: 行き 4km/h・帰り 6km/h の往復で計 1 時間。片道 d は?
-- 立式: d/4 + d/6 = 1。解いて d = 12/5 = 2.4 km。
example (d : ℚ) : d / 4 + d / 6 = 1 ↔ d = 12 / 5 := by
  constructor
  · intro h; linarith
  · rintro rfl; norm_num
-- BOOK: end word-problem

-- BOOK: begin quad-ineq
-- 2次不等式を「解く」: x² − 5x + 6 < 0 ⟺ 2 < x < 3
example (x : ℝ) : x ^ 2 - 5 * x + 6 < 0 ↔ 2 < x ∧ x < 3 := by
  constructor
  · intro h
    constructor
    · nlinarith [sq_nonneg (x - 2)]
    · nlinarith [sq_nonneg (x - 3)]
  · rintro ⟨h2, h3⟩
    nlinarith [mul_pos (sub_pos.mpr h2) (sub_pos.mpr h3)]
-- BOOK: end quad-ineq

-- BOOK: begin quad-minmax
-- 区間 [0, 3] 上の x² − 2x: 最小 −1(x=1)、最大 3(x=3)
example (x : ℝ) (h1 : 0 ≤ x) (h2 : x ≤ 3) :
    -1 ≤ x ^ 2 - 2 * x ∧ x ^ 2 - 2 * x ≤ 3 := by
  constructor
  · nlinarith [sq_nonneg (x - 1)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr h2)
      (by linarith : (0 : ℝ) ≤ x + 1)]
-- BOOK: end quad-minmax

-- BOOK: begin quad-vieta
-- 解と係数の関係: 和が α+β、積が αβ の2次式は (x−α)(x−β)
example (x α β : ℚ) :
    x ^ 2 - (α + β) * x + α * β = (x - α) * (x - β) := by
  ring
-- BOOK: end quad-vieta

end Handbook.C07
