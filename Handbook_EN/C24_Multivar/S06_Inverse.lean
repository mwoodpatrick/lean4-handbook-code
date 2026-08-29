/- English edition source: Handbook/C24_Multivar/S06_Inverse.lean. -/
import Mathlib

namespace Handbook.C24

-- BOOK: begin inverse-strict
-- A condition stronger than HasFDerivAt, required by the inverse
-- function theorem
#check @HasStrictFDerivAt

-- Being of class C¹ gives the strict derivative automatically
#check @ContDiffAt.hasStrictFDerivAt
-- BOOK: end inverse-strict

-- BOOK: begin inverse-local
-- If the derivative is invertible (≃L) a local inverse can be built
#check @HasStrictFDerivAt.localInverse

-- The local inverse really is an inverse near the point a
example (f : ℝ × ℝ → ℝ × ℝ) (f' : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (a : ℝ × ℝ) (hf : HasStrictFDerivAt f (f' : ℝ × ℝ →L[ℝ] ℝ × ℝ) a) :
    ∀ᶠ x in nhds a, hf.localInverse f f' a (f x) = x :=
  hf.eventually_left_inverse
-- BOOK: end inverse-local

-- BOOK: begin inverse-deriv
-- The total derivative of the inverse is the inverse of the total
-- derivative
example (f : ℝ × ℝ → ℝ × ℝ) (f' : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (a : ℝ × ℝ) (hf : HasStrictFDerivAt f (f' : ℝ × ℝ →L[ℝ] ℝ × ℝ) a) :
    HasStrictFDerivAt (hf.localInverse f f' a)
      (f'.symm : ℝ × ℝ →L[ℝ] ℝ × ℝ) (f a) :=
  hf.to_localInverse
-- BOOK: end inverse-deriv

-- BOOK: begin implicit-data
-- The implicit function theorem is assembled from this structure
#check @ImplicitFunctionData
-- BOOK: end implicit-data

end Handbook.C24
