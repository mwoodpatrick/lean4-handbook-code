/- 第36章 多様体
   36.6 Lie 群 -/
import Mathlib

namespace Handbook.C36

open Manifold

-- BOOK: begin lie-group
-- Lie 群: 群演算が滑らかな多様体。群と幾何が同時に載る
#check @LieGroup

-- 加法版。ℝ は加法について Lie 群である
example : LieAddGroup (modelWithCornersSelf ℝ ℝ) ⊤ ℝ := by
  infer_instance
-- BOOK: end lie-group

-- BOOK: begin lie-circle
-- 円周群 Circle は絶対値 1 の複素数のなす群
example (z : Circle) : ‖(z : ℂ)‖ = 1 :=
  Circle.norm_coe z

-- 1次元多様体でもある。チャートは EuclideanSpace ℝ (Fin 1)
noncomputable example :
    ChartedSpace (EuclideanSpace ℝ (Fin 1)) Circle := by
  infer_instance

-- そして乗法について Lie 群になる
example : LieGroup
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) ⊤ Circle := by
  infer_instance
-- BOOK: end lie-circle

end Handbook.C36
