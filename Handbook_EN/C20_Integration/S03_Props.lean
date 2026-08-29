/- Chapter 20: Integration
   20.3 Properties of the integral -/
import Mathlib

open intervalIntegral MeasureTheory

namespace Handbook.C20

-- BOOK: begin int-linear
-- Linearity: the integral of a sum is the sum of the integrals
#check @intervalIntegral.integral_add
-- a constant factor comes out too
#check @intervalIntegral.integral_smul
-- BOOK: end int-linear

-- BOOK: begin int-additive
-- Additivity in the interval: joining [a,b] and [b,c] gives [a,c]
#check @intervalIntegral.integral_add_adjacent_intervals
-- BOOK: end int-additive

-- BOOK: begin int-mono
-- Monotonicity: f ≤ g gives ≤ for the integrals, the start of estimates
example (f g : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hg : IntervalIntegrable g MeasureTheory.volume a b)
    (h : ∀ x ∈ Set.Icc a b, f x ≤ g x) :
    ∫ x in a..b, f x ≤ ∫ x in a..b, g x :=
  intervalIntegral.integral_mono_on hab hf hg h
-- BOOK: end int-mono

-- BOOK: begin int-abs
-- The triangle inequality for integrals: |∫f| ≤ ∫|f|
#check @intervalIntegral.abs_integral_le_integral_abs
-- BOOK: end int-abs

end Handbook.C20
