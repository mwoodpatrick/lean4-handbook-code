/- Chapter 10: Trigonometric functions
   10.1 Radians and the definitions -/
import Mathlib

open Real

namespace Handbook.C10

-- BOOK: begin trig-pi
-- π itself is defined as a real constant
#check π                -- Real.pi : ℝ
#check Real.pi_pos      -- 0 < π
-- BOOK: end trig-pi

-- BOOK: begin trig-deg
-- Radians to degrees (× 180/π): π/6 is 30°
example : π / 6 * (180 / π) = 30 := by
  field_simp [Real.pi_ne_zero]
  ring
-- BOOK: end trig-deg

-- BOOK: begin trig-values
-- The values at the special angles are all registered as theorems
example : Real.sin 0 = 0 := Real.sin_zero
example : Real.cos 0 = 1 := Real.cos_zero
example : Real.sin (π / 2) = 1 := Real.sin_pi_div_two
example : Real.sin (π / 6) = 1 / 2 := Real.sin_pi_div_six
-- BOOK: end trig-values

-- BOOK: begin trig-tan
-- tan is defined as the ratio of sin to cos
example (x : ℝ) : Real.tan x = Real.sin x / Real.cos x :=
  Real.tan_eq_sin_div_cos x

-- a slope of 45° is 1
example : Real.tan (π / 4) = 1 := Real.tan_pi_div_four
-- BOOK: end trig-tan

end Handbook.C10
