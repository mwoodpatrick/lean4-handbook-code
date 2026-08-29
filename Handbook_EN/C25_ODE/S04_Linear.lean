/- English edition source: Handbook/C25_ODE/S04_Linear.lean. -/
import Mathlib

namespace Handbook.C25

-- BOOK: begin linear-scalar
-- For scalar: (e^{at})' = a·e^{at}.
-- The defining property of the exponential function is that its rate of
-- change is proportional to its current value.
example (a t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (a * s))
      (a * Real.exp (a * t)) t := by
  have h := (Real.hasDerivAt_exp (a * t)).comp t
    ((hasDerivAt_id t).const_mul a)
  simpa [Function.comp_def, mul_comm] using h
-- BOOK: end linear-scalar

-- BOOK: begin linear-exp
-- The matrix exponential is a special case of the exponential of a
-- Banach algebra
#check @NormedSpace.exp

-- It is defined by a power series (Chapter 21)
#check @NormedSpace.exp_eq_tsum
-- BOOK: end linear-exp

-- BOOK: begin linear-deriv
-- (e^{tA})' = A·e^{tA}: the solution of ẋ = Ax is e^{tA}x₀
#check @hasDerivAt_exp_smul_const
-- BOOK: end linear-deriv

-- BOOK: begin linear-commute
-- e^{A+B} = e^A·e^B holds only when A and B commute.
-- Matrix multiplication is not commutative, so the hypothesis stays.
#check @NormedSpace.exp_add_of_commute
-- BOOK: end linear-commute

end Handbook.C25
