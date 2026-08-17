/- 第26章 複素解析
   26.5 複素べき級数と指数関数 / 26.6 複素対数 -/
import Mathlib

namespace Handbook.C26

open Complex

-- BOOK: begin exp-decompose
-- e^z を実部と虚部に分解する。実部が大きさ、虚部が回転を担う
#check @Complex.exp_eq_exp_re_mul_sin_add_cos

-- 絶対値は実部だけで決まる: |e^z| = e^(Re z)
example (z : ℂ) : ‖exp z‖ = Real.exp z.re :=
  Complex.norm_exp z
-- BOOK: end exp-decompose

-- BOOK: begin exp-nonzero
-- e^z は決して 0 にならない(実指数関数と同じ)
example (z : ℂ) : exp z ≠ 0 :=
  Complex.exp_ne_zero z

-- しかし実指数関数と違い、単射でない: 周期 2πi を持つ
example : Function.Periodic exp (2 * Real.pi * I) :=
  Complex.exp_periodic
-- BOOK: end exp-nonzero

-- BOOK: begin log-branch
-- 対数は主枝で定義される。偏角を (-π, π] に制限して一価にする
#check @Complex.log
#check @Complex.arg_mem_Ioc

-- 0 でなければ exp と log は逆になる
example (z : ℂ) (hz : z ≠ 0) : exp (log z) = z :=
  Complex.exp_log hz
-- BOOK: end log-branch

end Handbook.C26
