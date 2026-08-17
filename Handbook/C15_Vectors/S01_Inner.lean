/- 第15章 ベクトル
   15.1 演算 / 15.2 内積と角 / 15.3 平行・垂直 -/
import Mathlib

namespace Handbook.C15

open scoped RealInnerProductSpace

-- BOOK: begin vec-inner
-- 内積は対称
example (x y : EuclideanSpace ℝ (Fin 2)) :
    ⟪x, y⟫ = ⟪y, x⟫ :=
  real_inner_comm y x

-- コーシー–シュワルツの不等式
example (x y : EuclideanSpace ℝ (Fin 2)) :
    |⟪x, y⟫| ≤ ‖x‖ * ‖y‖ :=
  abs_real_inner_le_norm x y
-- BOOK: end vec-inner

-- BOOK: begin vec-perp
-- 垂直(内積 0)なら三平方の定理が成り立つ
example (x y : EuclideanSpace ℝ (Fin 2)) (h : ⟪x, y⟫ = 0) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [norm_add_sq_real, h]
  ring
-- BOOK: end vec-perp

-- BOOK: begin vec-ops
-- 和とスカラー倍は成分ごと。ノルムの斉次性と三角不等式。
example (x : EuclideanSpace ℝ (Fin 2)) (c : ℝ) :
    ‖c • x‖ = |c| * ‖x‖ :=
  norm_smul c x

example (x y : EuclideanSpace ℝ (Fin 2)) :
    ‖x + y‖ ≤ ‖x‖ + ‖y‖ :=
  norm_add_le x y
-- BOOK: end vec-ops

-- BOOK: begin vec-parallelogram
-- 中線定理(平行四辺形の法則): 対角線の2乗和 = 辺の2乗和の2倍
example (x y : EuclideanSpace ℝ (Fin 2)) :
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := parallelogram_law_with_norm ℝ x y
  rw [pow_two, pow_two, pow_two, pow_two]
  linarith [h]
-- BOOK: end vec-parallelogram

-- BOOK: begin vec-unit
-- 正規化: ノルムで割れば長さ 1 の単位ベクトルになる
example (x : EuclideanSpace ℝ (Fin 2)) (hx : x ≠ 0) :
    ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 :=
  norm_smul_inv_norm hx
-- BOOK: end vec-unit

end Handbook.C15
