/- English edition source: Handbook/C26_Complex/S02_Holo.lean. -/
import Mathlib

namespace Handbook.C26

-- BOOK: begin holo-example
-- A polynomial is holomorphic on the whole plane (an entire function)
example : Differentiable ℂ (fun z : ℂ => z ^ 2 + 2 * z + 1) := by
  fun_prop

-- Holomorphy is differentiability over ℂ; the point is that the
-- scalar field ℂ is specified
#check @DifferentiableAt
-- BOOK: end holo-example

-- BOOK: begin holo-real
-- Complex differentiable implies differentiable as a function of
-- two real variables (the Cauchy--Riemann side)
#check @HasDerivAt.real_of_complex

-- Conjugation is ℝ-linear but not ℂ-linear, so it is not holomorphic
#check @Complex.conjCLE
-- BOOK: end holo-real

-- BOOK: begin holo-rigid
-- Rigidity: differentiable once means the derivative is holomorphic
-- too, unlike C¹ to C² for real functions
example (f : ℂ → ℂ) (h : Differentiable ℂ f) :
    Differentiable ℂ (deriv f) :=
  h.deriv
-- BOOK: end holo-rigid

end Handbook.C26
