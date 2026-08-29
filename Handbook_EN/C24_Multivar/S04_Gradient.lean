/- English edition source: Handbook/C24_Multivar/S04_Gradient.lean. -/
import Mathlib

namespace Handbook.C24

-- BOOK: begin gradient-def
-- The gradient is defined only on an inner product space
-- (an inner product is required)
#check @gradient

-- HasGradientAt f g x says that the total derivative is the linear
-- map taking the inner product with g
example {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] (f : F → ℝ) (g x : F) :
    HasGradientAt f g x ↔
      HasFDerivAt f (InnerProductSpace.toDual ℝ F g) x :=
  hasGradientAt_iff_hasFDerivAt
-- BOOK: end gradient-def

-- BOOK: begin gradient-line
-- In one dimension the gradient reduces to the derivative
#check @gradient_eq_deriv
-- BOOK: end gradient-line

end Handbook.C24
