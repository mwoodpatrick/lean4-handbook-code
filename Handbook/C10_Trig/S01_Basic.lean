/- 第10章 三角関数
   10.1 弧度法と単位円 / 10.2 sin と cos の定義 -/
import Mathlib

namespace Handbook.C10

open Real

-- BOOK: begin trig-values
-- 特別な角の値はすべて定理として登録されている
example : Real.sin 0 = 0 := Real.sin_zero
example : Real.cos 0 = 1 := Real.cos_zero
example : Real.sin (π / 2) = 1 := Real.sin_pi_div_two
example : Real.sin (π / 6) = 1 / 2 := Real.sin_pi_div_six
-- BOOK: end trig-values

-- BOOK: begin trig-pi
-- π そのものも実数の定数として定義されている
#check π          -- Real.pi : ℝ
#check Real.pi_pos -- 0 < π
-- BOOK: end trig-pi

-- BOOK: begin trig-tan
-- tan は sin と cos の比として定義される
example (x : ℝ) : Real.tan x = Real.sin x / Real.cos x :=
  Real.tan_eq_sin_div_cos x

-- 45° の傾きは 1
example : Real.tan (π / 4) = 1 := Real.tan_pi_div_four
-- BOOK: end trig-tan

-- BOOK: begin trig-deg
-- 弧度法 → 度数法の換算(×180/π): π/6 は 30°
example : π / 6 * (180 / π) = 30 := by
  field_simp [Real.pi_ne_zero]
  ring
-- BOOK: end trig-deg

end Handbook.C10
