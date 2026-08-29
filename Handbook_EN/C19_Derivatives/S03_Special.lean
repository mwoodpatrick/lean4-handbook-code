/- English edition source: Handbook/C19_Derivatives/S03_Special.lean. -/
import Mathlib

namespace Handbook.C19

-- BOOK: begin deriv-special
-- Up to constant multiples, exp is the unique function unchanged by
-- differentiation
example : deriv Real.exp = Real.exp := by
  funext x
  exact (Real.hasDerivAt_exp x).deriv

-- (sin)' = cos
example : deriv Real.sin = Real.cos := Real.deriv_sin
-- BOOK: end deriv-special

-- BOOK: begin deriv-iterated
-- Higher derivatives: the second derivative of sin is -sin
example (x : ℝ) :
    deriv (deriv Real.sin) x = -Real.sin x := by
  rw [Real.deriv_sin, Real.deriv_cos]
-- BOOK: end deriv-iterated

-- BOOK: begin deriv-exp-char
-- exp is “its own derivative” --- pointwise as well
example (x : ℝ) : deriv Real.exp x = Real.exp x := by
  rw [Real.deriv_exp]

-- (cos)' = -sin
example : deriv Real.cos = fun x => -Real.sin x :=
  Real.deriv_cos'
-- BOOK: end deriv-exp-char

end Handbook.C19
