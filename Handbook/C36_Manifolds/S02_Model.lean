/- 第36章 多様体
   36.3 mathlib の多様体(ModelWithCorners の設計思想)-/
import Mathlib

namespace Handbook.C36

open Manifold

-- BOOK: begin model-with-corners
-- ModelWithCorners: モデル空間とその中の「住む場所」を組にする
#check @ModelWithCorners

-- 境界のない場合は自明モデル。全空間に住む
noncomputable example : ModelWithCorners ℝ ℝ ℝ :=
  modelWithCornersSelf ℝ ℝ

-- ユークリッド空間版。次元をパラメータで持つ
noncomputable example (n : ℕ) :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n)) :=
  modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))
-- BOOK: end model-with-corners

-- BOOK: begin is-manifold
-- IsManifold: チャートの張り合わせが滑らかであること
#check @IsManifold

-- ℝ は自明モデルの上の C^∞ 多様体である
example : IsManifold (modelWithCornersSelf ℝ ℝ) ⊤ ℝ := by
  infer_instance
-- BOOK: end is-manifold

end Handbook.C36
