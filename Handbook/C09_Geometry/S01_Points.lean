/- 第9章 平面図形と初等幾何
   9.1 点・距離・角 -/
import Mathlib

namespace Handbook.C09

-- BOOK: begin geo-points
-- 平面 = EuclideanSpace ℝ (Fin 2)。点は座標から !₂[x, y] で作る。
def P : EuclideanSpace ℝ (Fin 2) := !₂[0, 0]
def Q : EuclideanSpace ℝ (Fin 2) := !₂[3, 4]

-- 2点間の距離はユークリッド距離。3-4-5 の直角三角形なので
-- 距離の2乗は 3² + 4² = 25(距離そのものは √25 = 5)。
example : dist P Q ^ 2 = 25 := by
  rw [P, Q, EuclideanSpace.dist_eq, Real.sq_sqrt]
  · norm_num [Fin.sum_univ_two]
  · positivity
-- BOOK: end geo-points

-- BOOK: begin geo-dist-axioms
-- 距離の3公理: 対称性・非退化・三角不等式
example (a b : EuclideanSpace ℝ (Fin 2)) : dist a b = dist b a :=
  dist_comm a b

example (a b : EuclideanSpace ℝ (Fin 2)) : dist a b = 0 ↔ a = b :=
  dist_eq_zero

example (a b c : EuclideanSpace ℝ (Fin 2)) :
    dist a c ≤ dist a b + dist b c :=
  dist_triangle a b c
-- BOOK: end geo-dist-axioms

-- BOOK: begin geo-dist-five
-- 距離そのものも確定できる: d² = 25 と d ≥ 0 から d = 5
example : dist P Q = 5 := by
  have h2 : dist P Q ^ 2 = 25 := by
    rw [P, Q, EuclideanSpace.dist_eq, Real.sq_sqrt]
    · norm_num [Fin.sum_univ_two]
    · positivity
  have hnn : 0 ≤ dist P Q := dist_nonneg
  have h3 : (dist P Q - 5) * (dist P Q + 5) = 0 := by nlinarith
  rcases mul_eq_zero.mp h3 with h4 | h4
  · linarith
  · linarith
-- BOOK: end geo-dist-five

-- BOOK: begin geo-isometry
-- 平行移動は距離を保つ(等長写像)。合同の現代的な言い換え。
example (a b v : EuclideanSpace ℝ (Fin 2)) :
    dist (a + v) (b + v) = dist a b :=
  dist_add_right a b v
-- BOOK: end geo-isometry

-- BOOK: begin geo-line
-- 2点 (1,2), (3,8) を通る直線: 傾きは (8−2)/(3−1) = 3
#eval ((8 - 2 : ℚ) / (3 - 1))  -- 出力: 3

-- 直線 y = 3x − 1 が確かに2点を通ることの検算
example : (3 : ℚ) * 1 - 1 = 2 ∧ (3 : ℚ) * 3 - 1 = 8 := by
  norm_num
-- BOOK: end geo-line

end Handbook.C09
