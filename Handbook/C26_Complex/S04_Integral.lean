/- 第26章 複素解析
   26.7 経路積分と Cauchy の積分定理 / 26.8 積分公式と解析性 -/
import Mathlib

namespace Handbook.C26

open Complex Metric

-- BOOK: begin integral-key
-- すべての出発点: 中心のまわりの 1/(z-c) の積分は 2πi。
-- 半径にも中心にも依らないこの値が、以降の公式を生む
example (c : ℂ) {R : ℝ} (hR : R ≠ 0) :
    (∮ z in C(c, R), (z - c)⁻¹) = 2 * Real.pi * I :=
  circleIntegral.integral_sub_center_inv c hR
-- BOOK: end integral-key

-- BOOK: begin integral-cauchy
-- Cauchy の積分定理: 円板で正則・閉円板で連続なら、
-- 円周上の積分は 0 になる
example {R : ℝ} (hR : 0 ≤ R) {f : ℂ → ℂ} {c : ℂ}
    (hf : DiffContOnCl ℂ f (ball c R)) :
    (∮ z in C(c, R), f z) = 0 :=
  hf.circleIntegral_eq_zero hR
-- BOOK: end integral-cauchy

-- BOOK: begin integral-formula
-- Cauchy の積分公式: 内部の値が境界上の積分で復元される
#check @DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul
-- BOOK: end integral-formula

-- BOOK: begin integral-analytic
-- 奇跡の本体: 正則なら解析的(べき級数に展開できる)
#check @DiffContOnCl.hasFPowerSeriesOnBall

example {s : Set ℂ} {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f s)
    (ho : IsOpen s) : AnalyticOnNhd ℂ f s :=
  hd.analyticOnNhd ho
-- BOOK: end integral-analytic

end Handbook.C26
