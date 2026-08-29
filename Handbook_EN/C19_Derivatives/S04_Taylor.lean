/- English edition source: Handbook/C19_Derivatives/S04_Taylor.lean. -/
import Mathlib

namespace Handbook.C19

-- BOOK: begin taylor-lagrange
-- Taylor’s theorem (Lagrange remainder).
-- The c in the remainder is like the c in the MVT: its value is not
-- known
#check @taylor_mean_remainder_lagrange

-- Polynomial part, giving the approximation through degree n
#check @taylorWithinEval
-- BOOK: end taylor-lagrange

-- BOOK: begin lhopital
-- l’Hôpital’s rule replaces a 0/0 limit by the ratio of derivatives
#check @HasDerivAt.lhopital_zero_nhds

-- A separate form is provided for limits at infinity
#check @deriv.lhopital_zero_atTop
-- BOOK: end lhopital

-- BOOK: begin contdiff
-- Classes C^n and C^∞. A type-class argument expresses how often
-- differentiation is possible.
#check @ContDiff

-- Higher derivatives
#check @iteratedDeriv
-- BOOK: end contdiff

-- BOOK: begin diff-cont
-- Differentiability implies continuity; the converse fails (|x| is a
-- counterexample)
example (f : ℝ → ℝ) (x : ℝ) (h : DifferentiableAt ℝ f x) :
    ContinuousAt f x :=
  h.continuousAt
-- BOOK: end diff-cont

end Handbook.C19
