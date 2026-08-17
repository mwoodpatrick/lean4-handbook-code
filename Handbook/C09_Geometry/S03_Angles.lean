/- 第9章 平面図形と初等幾何
   9.1 角の基本性質 -/
import Mathlib

namespace Handbook.C09

open EuclideanGeometry Real

-- BOOK: begin geo-angle
-- 角 ∠ a b c は頂点 b から見た a, c 方向のなす角(0 から π)
example (a b c : EuclideanSpace ℝ (Fin 2)) :
    ∠ a b c = ∠ c b a :=
  EuclideanGeometry.angle_comm a b c

example (a b c : EuclideanSpace ℝ (Fin 2)) :
    ∠ a b c ≤ π :=
  EuclideanGeometry.angle_le_pi a b c

example (a b c : EuclideanSpace ℝ (Fin 2)) :
    0 ≤ ∠ a b c :=
  EuclideanGeometry.angle_nonneg a b c
-- BOOK: end geo-angle

-- BOOK: begin geo-angle-sum
-- 三角形の内角の和は π。仮定は「2頂点が異なる」だけでよい
-- (3点が一直線に潰れた「退化三角形」でも成り立つ)。
example (a b c : EuclideanSpace ℝ (Fin 2)) (h : b ≠ a) :
    ∠ a b c + ∠ b c a + ∠ c a b = π :=
  angle_add_angle_add_angle_eq_pi c h
-- BOOK: end geo-angle-sum

end Handbook.C09
