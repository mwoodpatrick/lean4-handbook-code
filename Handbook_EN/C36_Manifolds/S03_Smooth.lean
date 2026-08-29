/- English edition source: Handbook/C36_Manifolds/S03_Smooth.lean. -/
import Mathlib

namespace Handbook.C36

open Manifold

/-- A trivial one-dimensional model over ℝ, used to shorten notation. -/
noncomputable abbrev I1 : ModelWithCorners ℝ ℝ ℝ := modelWithCornersSelf ℝ ℝ

-- BOOK: begin smooth-basic
-- The identity is smooth. The third argument of ContMDiff is the
-- order of differentiability.
example : ContMDiff I1 I1 ⊤ (id : ℝ → ℝ) :=
  contMDiff_id

-- a constant map is smooth
example (c : ℝ) : ContMDiff I1 I1 ⊤ (fun _ : ℝ => c) :=
  contMDiff_const
-- BOOK: end smooth-basic

-- BOOK: begin smooth-comp
-- a composition of smooth maps is smooth
example (f g : ℝ → ℝ) (hf : ContMDiff I1 I1 ⊤ f)
    (hg : ContMDiff I1 I1 ⊤ g) : ContMDiff I1 I1 ⊤ (g ∘ f) :=
  hg.comp hf

-- smooth implies continuous (Chapter 32)
example (f : ℝ → ℝ) (hf : ContMDiff I1 I1 ⊤ f) : Continuous f :=
  hf.continuous
-- BOOK: end smooth-comp

end Handbook.C36
