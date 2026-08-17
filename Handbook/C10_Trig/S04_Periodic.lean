/- 第10章 三角関数
   10.5 周期性とグラフ -/
import Mathlib

namespace Handbook.C10

open Real

-- BOOK: begin trig-periodic
-- 周期 2π
example (x : ℝ) : Real.sin (x + 2 * π) = Real.sin x :=
  Real.sin_add_two_pi x

-- 偶関数・奇関数
example (x : ℝ) : Real.cos (-x) = Real.cos x := Real.cos_neg x
example (x : ℝ) : Real.sin (-x) = -Real.sin x := Real.sin_neg x
-- BOOK: end trig-periodic

-- BOOK: begin trig-shift
-- 平行移動の関係: cos は sin を π/2 ずらしたもの
example (x : ℝ) : Real.cos x = Real.sin (x + π / 2) :=
  (Real.sin_add_pi_div_two x).symm
-- BOOK: end trig-shift

end Handbook.C10
