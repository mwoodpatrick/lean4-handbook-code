/- English edition source: Handbook/C34_Functional/S06_Spectrum.lean. -/
import Mathlib

namespace Handbook.C34

-- BOOK: begin spectrum-def
-- The spectrum: the set of μ for which a − μ is not invertible,
-- the generalization of eigenvalues
example (A : Type) [NormedRing A] [NormedAlgebra ℂ A] (a : A) :
    spectrum ℂ a = {μ : ℂ | ¬IsUnit (algebraMap ℂ A μ - a)} :=
  rfl
-- BOOK: end spectrum-def

-- BOOK: begin spectrum-nonempty
-- Over a complex Banach algebra the spectrum is always non-empty
example (A : Type) [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [Nontrivial A] (a : A) :
    (spectrum ℂ a).Nonempty :=
  spectrum.nonempty a
-- BOOK: end spectrum-nonempty

-- BOOK: begin spectrum-bounded
-- the spectrum fits inside the closed disc of radius ‖a‖
example (A : Type) [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [NormOneClass A] (a : A) :
    spectrum ℂ a ⊆ Metric.closedBall 0 ‖a‖ :=
  spectrum.subset_closedBall_norm a
-- BOOK: end spectrum-bounded

end Handbook.C34
