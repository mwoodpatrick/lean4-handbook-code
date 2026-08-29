/- English edition source: Handbook/C24_Multivar/S02_Partial.lean. -/
import Mathlib

namespace Handbook.C24

-- BOOK: begin partial-slice
-- Fixing y = b, the section t ↦ t·b is a one-variable function.
-- Its derivative b is the x partial derivative of f(x,y) = xy.
example (b x : ℝ) : HasDerivAt (fun t : ℝ => t * b) b x := by
  simpa using (hasDerivAt_id x).mul_const b
-- BOOK: end partial-slice

-- BOOK: begin partial-product
-- The total derivative of f(x,y) = xy. At (a,b) the coefficients
-- are the two partial derivatives.

example (a b : ℝ) :
    HasFDerivAt (fun p : ℝ × ℝ => p.1 * p.2)
      (a • ContinuousLinearMap.snd ℝ ℝ ℝ
        + b • ContinuousLinearMap.fst ℝ ℝ ℝ) (a, b) := by
  -- the product rule; without naming the point (a, b) unification fails
  have h := (hasFDerivAt_fst (𝕜 := ℝ) (p := (a, b))).mul
    (hasFDerivAt_snd (𝕜 := ℝ) (p := (a, b)))
  exact h
-- BOOK: end partial-product

-- BOOK: begin line-deriv
-- Directional derivative: the rate of change when moving from point x
-- in direction v.
#check @lineDeriv

-- Given a total derivative, the directional derivative exists in
-- every direction v, and its value is L v
example (f : ℝ × ℝ → ℝ) (L : ℝ × ℝ →L[ℝ] ℝ) (x v : ℝ × ℝ)
    (hf : HasFDerivAt f L x) : HasLineDerivAt ℝ f (L v) x v :=
  hf.hasLineDerivAt v
-- BOOK: end line-deriv

-- BOOK: begin line-deriv-zero
-- lineDeriv returns 0 when the directional derivative does not
-- exist, so a returned 0 does not mean the rate of change is 0
#check @lineDeriv_zero_of_not_lineDifferentiableAt
-- BOOK: end line-deriv-zero

end Handbook.C24
