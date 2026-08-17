/- 第9章 平面図形と初等幾何
   9.3 三平方の定理 / 9.4 余弦定理 -/
import Mathlib

namespace Handbook.C09

open EuclideanGeometry Real

-- BOOK: begin geo-lawcos
-- 余弦定理。mathlib の一般形(距離は積の形で書かれる)。
example (a b c : EuclideanSpace ℝ (Fin 2)) :
    dist a c * dist a c =
      dist a b * dist a b + dist c b * dist c b
        - 2 * dist a b * dist c b * Real.cos (∠ a b c) :=
  EuclideanGeometry.law_cos a b c
-- BOOK: end geo-lawcos

-- BOOK: begin geo-pythagoras
-- 三平方の定理: 角 B が直角なら AC² = AB² + CB²。
-- 余弦定理で cos(π/2) = 0 とするだけで従う。
theorem pythagoras (a b c : EuclideanSpace ℝ (Fin 2))
    (h : ∠ a b c = π / 2) :
    dist a c ^ 2 = dist a b ^ 2 + dist c b ^ 2 := by
  have hlc := EuclideanGeometry.law_cos a b c
  rw [h, Real.cos_pi_div_two, mul_zero, sub_zero] at hlc
  rw [pow_two, pow_two, pow_two]
  exact hlc
-- BOOK: end geo-pythagoras

-- BOOK: begin geo-apollonius
-- 中線定理(アポロニウスの定理):
-- AB² + AC² = 2(AM² + (BC/2)²)、M は BC の中点
example (a b c : EuclideanSpace ℝ (Fin 2)) :
    dist a b ^ 2 + dist a c ^ 2 =
      2 * (dist a (midpoint ℝ b c) ^ 2 + (dist b c / 2) ^ 2) :=
  dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq
    a b c
-- BOOK: end geo-apollonius

end Handbook.C09
