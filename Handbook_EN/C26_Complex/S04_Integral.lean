/- English edition source: Handbook/C26_Complex/S04_Integral.lean. -/
import Mathlib

namespace Handbook.C26

open Complex Metric

-- BOOK: begin integral-key
-- The starting point: the integral of 1/(z−c) around its center is
-- 2πi. It depends on neither the radius nor the center.
example (c : ℂ) {R : ℝ} (hR : R ≠ 0) :
    (∮ z in C(c, R), (z - c)⁻¹) = 2 * Real.pi * I :=
  circleIntegral.integral_sub_center_inv c hR
-- BOOK: end integral-key

-- BOOK: begin integral-cauchy
-- Cauchy's integral theorem: for a function holomorphic on a disc
-- and continuous on its closure, the integral over the circle is 0
example {R : ℝ} (hR : 0 ≤ R) {f : ℂ → ℂ} {c : ℂ}
    (hf : DiffContOnCl ℂ f (ball c R)) :
    (∮ z in C(c, R), f z) = 0 :=
  hf.circleIntegral_eq_zero hR
-- BOOK: end integral-cauchy

-- BOOK: begin integral-formula
-- Cauchy’s integral formula: an interior value is recovered from an
-- integral over the boundary.
#check @DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul
-- BOOK: end integral-formula

-- BOOK: begin integral-analytic
-- The miracle: holomorphic implies analytic (expandable in a power
-- series)
#check @DiffContOnCl.hasFPowerSeriesOnBall

example {s : Set ℂ} {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f s)
    (ho : IsOpen s) : AnalyticOnNhd ℂ f s :=
  hd.analyticOnNhd ho
-- BOOK: end integral-analytic

end Handbook.C26
