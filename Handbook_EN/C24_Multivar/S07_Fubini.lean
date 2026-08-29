/- English edition source: Handbook/C24_Multivar/S07_Fubini.lean. -/
import Mathlib

namespace Handbook.C24

open MeasureTheory

-- BOOK: begin fubini-volume
-- The volume measure of the plane is defined as a product of two
-- measures on the line
example : (volume : Measure (ℝ × ℝ))
    = (volume : Measure ℝ).prod (volume : Measure ℝ) :=
  Measure.volume_eq_prod ℝ ℝ

-- The measure of an interval is its length
example (a b : ℝ) : volume (Set.Icc a b) = ENNReal.ofReal (b - a) :=
  Real.volume_Icc
-- BOOK: end fubini-volume

-- BOOK: begin fubini-main
-- Fubini's theorem: the multiple integral equals the iterated one.
-- The integrability hypothesis is essential; without it the
-- conclusion is false.
#check @MeasureTheory.integral_prod
-- BOOK: end fubini-main

-- BOOK: begin fubini-swap
-- Exchanging the order of integration; note the integrability
-- hypothesis
example (f : ℝ → ℝ → ℝ)
    (hf : Integrable (Function.uncurry f) (volume.prod volume)) :
    ∫ x : ℝ, ∫ y : ℝ, f x y = ∫ y : ℝ, ∫ x : ℝ, f x y :=
  integral_integral_swap hf
-- BOOK: end fubini-swap

-- BOOK: begin fubini-change
-- The change of variables formula. Volume is scaled by the absolute
-- value of the Jacobian determinant.
#check @MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
-- BOOK: end fubini-change

end Handbook.C24
