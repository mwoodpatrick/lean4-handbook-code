/- English edition source: Handbook/C25_ODE/S02_Solve.lean. -/
import Mathlib

namespace Handbook.C25

-- BOOK: begin solve-separable
-- Separation of variables: ẋ = 2t x has the solution x(t) = C·e^{t²}
example (C t : ℝ) :
    HasDerivAt (fun s : ℝ => C * Real.exp (s ^ 2))
      (2 * t * (C * Real.exp (t ^ 2))) t := by
  have h : HasDerivAt (fun s : ℝ => Real.exp (s ^ 2))
      (Real.exp (t ^ 2) * (2 * t)) t := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (t ^ 2)).comp t (hasDerivAt_pow 2 t)
  have := h.const_mul C
  simpa [mul_comm, mul_assoc, mul_left_comm] using this
-- BOOK: end solve-separable

-- BOOK: begin solve-linear
-- The first-order linear equation ẋ = −x + 1 has the solution
-- x(t) = 1 + C·e^{−t}
example (C t : ℝ) :
    HasDerivAt (fun s : ℝ => 1 + C * Real.exp (-s))
      (-(1 + C * Real.exp (-t)) + 1) t := by
  have h : HasDerivAt (fun s : ℝ => Real.exp (-s))
      (-Real.exp (-t)) t := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)
  have := (h.const_mul C).const_add 1
  simpa [mul_comm] using this
-- BOOK: end solve-linear

-- BOOK: begin solve-ivp
-- The initial condition x(0) = x₀ determines the integration constant
-- C.
-- An initial value problem picks one solution out of the general one
example (x₀ : ℝ) : (fun s : ℝ => x₀ * Real.exp s) 0 = x₀ := by
  simp
-- BOOK: end solve-ivp

end Handbook.C25
