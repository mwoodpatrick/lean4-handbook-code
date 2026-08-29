/- Chapter 10: Trigonometric functions
   10.5 Trigonometric equations -/
import Mathlib

open Real

namespace Handbook.C10

-- BOOK: begin trig-eq
-- The solutions of sin x = 0 are exactly x = nπ for an integer n
example (x : ℝ) :
    Real.sin x = 0 ↔ ∃ n : ℤ, (n : ℝ) * π = x :=
  Real.sin_eq_zero_iff
-- BOOK: end trig-eq

-- BOOK: begin trig-eq-cos
-- The solutions of cos x = 1 are x = 2nπ
example (x : ℝ) :
    Real.cos x = 1 ↔ ∃ n : ℤ, (n : ℝ) * (2 * π) = x :=
  Real.cos_eq_one_iff x
-- BOOK: end trig-eq-cos

end Handbook.C10
