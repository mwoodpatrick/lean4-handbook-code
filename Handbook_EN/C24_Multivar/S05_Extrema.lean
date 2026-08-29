/- English edition source: Handbook/C24_Multivar/S05_Extrema.lean. -/
import Mathlib

namespace Handbook.C24

-- BOOK: begin extrema-min
-- The origin is a local minimum of f(x,y) = x² + y²
example : IsLocalMin (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) 0 :=
  Filter.Eventually.of_forall fun p => by simp; positivity
-- BOOK: end extrema-min

-- BOOK: begin extrema-fermat
-- The total derivative vanishes at an interior extremum
#check @IsLocalMin.fderiv_eq_zero
#check @IsLocalMax.fderiv_eq_zero

-- The convenient form: given the existence of the total derivative,
-- it is 0
example (f : ℝ × ℝ → ℝ) (f' : ℝ × ℝ →L[ℝ] ℝ) (x : ℝ × ℝ)
    (hmax : IsLocalMax f x) (hf : HasFDerivAt f f' x) : f' = 0 :=
  hmax.hasFDerivAt_eq_zero hf
-- BOOK: end extrema-fermat

-- BOOK: begin extrema-hessian
-- The second total derivative; the Hessian is its matrix as a
-- bilinear map
#check @iteratedFDeriv

-- Symmetry: mixed partials may be taken in either order
-- (Schwarz's theorem)
#check @second_derivative_symmetric
-- BOOK: end extrema-hessian

-- BOOK: begin extrema-convex
-- For a convex function a local minimum is a global one
#check @ConvexOn

-- it is at most the value at every other point
example (f : ℝ × ℝ → ℝ) (a : ℝ × ℝ) (hmin : IsLocalMin f a)
    (hconv : ConvexOn ℝ Set.univ f) : ∀ x, f a ≤ f x :=
  IsMinOn.of_isLocalMin_of_convex_univ hmin hconv
-- BOOK: end extrema-convex

-- BOOK: begin extrema-lagrange
-- Constrained extrema: the method of Lagrange multipliers.
-- At a constrained extremum, the two gradients are parallel.
#check @IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d
-- BOOK: end extrema-lagrange

end Handbook.C24
