/- Chapter 20: Integration
   20.2 The fundamental theorem of calculus -/
import Mathlib

open intervalIntegral MeasureTheory

namespace Handbook.C20

-- BOOK: begin ftc
-- The fundamental theorem: integrating a derivative gives a difference
example (f f' : ℝ → ℝ) (a b : ℝ)
    (h : ∀ x ∈ Set.uIcc a b, HasDerivAt f (f' x) x)
    (h' : IntervalIntegrable f' volume a b) :
    ∫ x in a..b, f' x = f b - f a :=
  integral_eq_sub_of_hasDerivAt h h'
-- BOOK: end ftc

-- BOOK: begin ftc-apply
-- An application: the integral of the derivative f' is the difference
-- of f at the endpoints (given an antiderivative F, ∫ F' = F b - F a)
example (F : ℝ → ℝ) (a b : ℝ)
    (hdiff : ∀ x ∈ Set.uIcc a b, DifferentiableAt ℝ F x)
    (hint : IntervalIntegrable (deriv F) volume a b) :
    ∫ x in a..b, deriv F x = F b - F a :=
  integral_deriv_eq_sub hdiff hint
-- BOOK: end ftc-apply

-- BOOK: begin byparts
-- Integration by parts, in general form (mathlib's declaration)
#check @intervalIntegral.integral_mul_deriv_eq_deriv_mul
-- BOOK: end byparts

end Handbook.C20
