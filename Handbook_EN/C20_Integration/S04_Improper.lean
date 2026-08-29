/- Chapter 20: Integration
   20.5 Substitution and improper integrals -/
import Mathlib

open intervalIntegral MeasureTheory

namespace Handbook.C20

-- BOOK: begin substitution
-- Substitution: the chain rule for composition, followed backwards
#check @intervalIntegral.integral_deriv_smul_comp
-- BOOK: end substitution

-- BOOK: begin log-integral
-- The integral of 1/x is a logarithm: an antiderivative in
-- elementary functions
example {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x in a..b, 1 / x = Real.log (b / a) :=
  integral_one_div_of_pos ha hb
-- BOOK: end log-integral

-- BOOK: begin improper
-- Integrals over infinite intervals: the fundamental theorem is
-- extended as a limit of interval integrals
#check @MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
-- integrability of x^p is decided by the value of p
#check @integrableOn_Ioi_rpow_iff
-- BOOK: end improper

-- BOOK: begin integrable-on
-- Integrability is a predicate; that the integral is finite has to
-- be said separately
#check @MeasureTheory.IntegrableOn
#check @IntervalIntegrable
-- BOOK: end integrable-on

end Handbook.C20
