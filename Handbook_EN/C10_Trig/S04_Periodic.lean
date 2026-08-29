/- Chapter 10: Trigonometric functions
   10.4 Periodicity and parity -/
import Mathlib

open Real

namespace Handbook.C10

-- BOOK: begin trig-periodic
-- Period 2π
example (x : ℝ) : Real.sin (x + 2 * π) = Real.sin x :=
  Real.sin_add_two_pi x

-- even and odd
example (x : ℝ) : Real.cos (-x) = Real.cos x := Real.cos_neg x
example (x : ℝ) : Real.sin (-x) = -Real.sin x := Real.sin_neg x
-- BOOK: end trig-periodic

-- BOOK: begin trig-shift
-- A relation by translation: cos is sin shifted by π/2
example (x : ℝ) : Real.cos x = Real.sin (x + π / 2) :=
  (Real.sin_add_pi_div_two x).symm
-- BOOK: end trig-shift

end Handbook.C10
