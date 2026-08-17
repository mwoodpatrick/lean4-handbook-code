/- 第26章 複素解析
   26.4 正則性と Cauchy–Riemann 方程式 -/
import Mathlib

namespace Handbook.C26

-- BOOK: begin holo-example
-- 多項式は全平面で正則(整関数)
example : Differentiable ℂ (fun z : ℂ => z ^ 2 + 2 * z + 1) := by
  fun_prop

-- 正則性は「ℂ 上の微分可能性」。係数体 ℂ を明示するのが要点
#check @DifferentiableAt
-- BOOK: end holo-example

-- BOOK: begin holo-real
-- 複素微分可能なら、ℝ 上の関数として見ても微分可能。
-- 逆は成り立たない(Cauchy–Riemann 方程式が要る)
#check @HasDerivAt.real_of_complex

-- 複素共役は ℝ 線形だが ℂ 線形でない。ゆえに正則でない
#check @Complex.conjCLE
-- BOOK: end holo-real

-- BOOK: begin holo-rigid
-- 剛性: 一度微分できれば、導関数もまた正則である。
-- 実関数では C¹ から C² は従わない
example (f : ℂ → ℂ) (h : Differentiable ℂ f) :
    Differentiable ℂ (deriv f) :=
  h.deriv
-- BOOK: end holo-rigid

end Handbook.C26
