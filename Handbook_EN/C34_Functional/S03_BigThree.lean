/- English edition source: Handbook/C34_Functional/S03_BigThree.lean. -/
import Mathlib

namespace Handbook.C34

-- BOOK: begin hahn-banach
-- Hahn--Banach: a functional on a subspace extends to the whole
-- space
example (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Subspace ℝ E) (f : StrongDual ℝ p) :
    ∃ g : StrongDual ℝ E, (∀ x : p, g x = f x) ∧ ‖g‖ = ‖f‖ :=
  exists_extension_norm_eq p f
-- BOOK: end hahn-banach

-- BOOK: begin uniform-bounded
-- Uniform boundedness principle: pointwise boundedness implies a
-- uniform bound on operator norms.
example (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace E]
    (ι : Type) (g : ι → E →L[ℝ] F)
    (h : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) :
    ∃ C', ∀ i, ‖g i‖ ≤ C' :=
  banach_steinhaus h
-- BOOK: end uniform-bounded

-- BOOK: begin open-mapping
-- The open mapping theorem: a surjective bounded linear operator is
-- an open map
#check @ContinuousLinearMap.isOpenMap

-- Consequently, the inverse of a bijective bounded linear operator is
-- bounded (the inverse mapping theorem).
#check @ContinuousLinearEquiv.ofBijective
-- BOOK: end open-mapping

end Handbook.C34
