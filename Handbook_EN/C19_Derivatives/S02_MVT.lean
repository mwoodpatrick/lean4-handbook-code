/- English edition source: Handbook/C19_Derivatives/S02_MVT.lean. -/
import Mathlib

namespace Handbook.C19

-- BOOK: begin mvt
-- Mean value theorem: somewhere in the interval, tangent slope =
-- average rate of change
example (f f' : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hfc : ContinuousOn f (Set.Icc a b))
    (hff' : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x) :
    ∃ c ∈ Set.Ioo a b, f' c = (f b - f a) / (b - a) :=
  exists_hasDerivAt_eq_slope f f' hab hfc hff'
-- BOOK: end mvt

-- BOOK: begin mvt-mono
-- Consequence: a positive derivative implies strict increase
example (f : ℝ → ℝ) (h : ∀ x, 0 < deriv f x) : StrictMono f :=
  strictMono_of_deriv_pos h
-- BOOK: end mvt-mono

-- BOOK: begin rolle
-- Rolle’s theorem: equal endpoint values imply an intermediate point
-- with f' = 0
example (f f' : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hfc : ContinuousOn f (Set.Icc a b))
    (hff' : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hfab : f a = f b) :
    ∃ c ∈ Set.Ioo a b, f' c = 0 :=
  exists_hasDerivAt_eq_zero hab hfc hfab hff'
-- BOOK: end rolle

-- BOOK: begin deriv-const-of
-- A function whose derivative is zero everywhere is constant (a
-- consequence of the MVT)
example (f : ℝ → ℝ) (hd : Differentiable ℝ f)
    (h : ∀ x, deriv f x = 0) : ∀ x y, f x = f y :=
  is_const_of_deriv_eq_zero hd h
-- BOOK: end deriv-const-of

end Handbook.C19
