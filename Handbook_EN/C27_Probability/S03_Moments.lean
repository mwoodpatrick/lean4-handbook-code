/- English edition source: Handbook/C27_Probability/S03_Moments.lean. -/
import Mathlib

namespace Handbook.C27

open MeasureTheory ProbabilityTheory

-- BOOK: begin expect-def
-- The expected value is the integral itself: the Lebesgue integral
-- of Chapter 33 used as it stands
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) :
    μ[X] = ∫ ω, X ω ∂μ :=
  rfl
-- BOOK: end expect-def

-- BOOK: begin variance-def
-- The variance is the expected value of the square of the deviation
-- from the mean
example {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    (hX : AEMeasurable X μ) :
    Var[X; μ] = ∫ ω, (X ω - μ[X]) ^ 2 ∂μ :=
  variance_eq_integral hX

-- The variance is nonnegative (it is the integral of a square)
example {Ω : Type} [MeasurableSpace Ω] (X : Ω → ℝ) (μ : Measure Ω) :
    0 ≤ Var[X; μ] :=
  variance_nonneg X μ
-- BOOK: end variance-def

-- BOOK: begin variance-scale
-- Scaling by c multiplies the variance by c² (the standard
-- deviation by |c|)
#check @ProbabilityTheory.variance_const_mul

-- the computational formula Var[X] = E[X²] − E[X]²
#check @ProbabilityTheory.variance_eq_sub
-- BOOK: end variance-scale

-- BOOK: begin chebyshev
-- Chebyshev's inequality: the probability of deviating from the mean
-- by c is at most Var/c².
-- The tail is bounded without assuming any distribution.
#check @ProbabilityTheory.meas_ge_le_variance_div_sq
-- BOOK: end chebyshev

-- BOOK: begin strong-law
-- The law of large numbers: for independent, identically distributed
-- variables the sample mean approaches the expected value
#check @ProbabilityTheory.strong_law_ae
-- BOOK: end strong-law

end Handbook.C27
