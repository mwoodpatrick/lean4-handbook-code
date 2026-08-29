/- English edition source: Handbook/C36_Manifolds/S02_Model.lean. -/
import Mathlib

namespace Handbook.C36

open Manifold

-- BOOK: begin model-with-corners
-- ModelWithCorners: pairs a model space with the region within it where
-- points live
#check @ModelWithCorners

-- With no boundary the model is the space itself, and every point
-- is interior
noncomputable example : ModelWithCorners ℝ ℝ ℝ :=
  modelWithCornersSelf ℝ ℝ

-- the Euclidean space version, with the dimension as a parameter
noncomputable example (n : ℕ) :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n)) :=
  modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))
-- BOOK: end model-with-corners

-- BOOK: begin is-manifold
-- IsManifold: the changes of chart are smooth
#check @IsManifold

-- ℝ with the self model is a C^∞ manifold
example : IsManifold (modelWithCornersSelf ℝ ℝ) ⊤ ℝ := by
  infer_instance
-- BOOK: end is-manifold

end Handbook.C36
