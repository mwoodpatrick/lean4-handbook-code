/- English edition source: Handbook/C26_Complex/S03_Series.lean. -/
import Mathlib

namespace Handbook.C26

open Complex

-- BOOK: begin exp-decompose
-- Decompose e^z into real and imaginary parts: the real part gives
-- the magnitude, the imaginary part the rotation
#check @Complex.exp_eq_exp_re_mul_sin_add_cos

-- The modulus is decided by the real part alone: ‖e^z‖ = e^(Re z)
example (z : ℂ) : ‖exp z‖ = Real.exp z.re :=
  Complex.norm_exp z
-- BOOK: end exp-decompose

-- BOOK: begin exp-nonzero
-- e^z is never 0 (as for the real exponential)
example (z : ℂ) : exp z ≠ 0 :=
  Complex.exp_ne_zero z

-- Unlike the real exponential it is not injective: it has period 2πi
example : Function.Periodic exp (2 * Real.pi * I) :=
  Complex.exp_periodic
-- BOOK: end exp-nonzero

-- BOOK: begin log-branch
-- The logarithm is defined by the principal branch, with the
-- argument restricted to (−π, π]
#check @Complex.log
#check @Complex.arg_mem_Ioc

-- for z ≠ 0, exp and log are inverse
example (z : ℂ) (hz : z ≠ 0) : exp (log z) = z :=
  Complex.exp_log hz
-- BOOK: end log-branch

end Handbook.C26
