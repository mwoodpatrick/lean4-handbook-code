/- 第24章 多変数の微積分
   24.8 重積分と Fubini の定理 -/
import Mathlib

namespace Handbook.C24

open MeasureTheory

-- BOOK: begin fubini-volume
-- 平面の体積測度は、直線の測度2つの直積として定義される
example : (volume : Measure (ℝ × ℝ))
    = (volume : Measure ℝ).prod (volume : Measure ℝ) :=
  Measure.volume_eq_prod ℝ ℝ

-- 長方形の面積は辺の長さの積
example (a b : ℝ) : volume (Set.Icc a b) = ENNReal.ofReal (b - a) :=
  Real.volume_Icc
-- BOOK: end fubini-volume

-- BOOK: begin fubini-main
-- Fubini の定理: 重積分は累次積分に一致する。
-- 仮定 Integrable が本質的で、外すと結論は偽になる
#check @MeasureTheory.integral_prod
-- BOOK: end fubini-main

-- BOOK: begin fubini-swap
-- 積分の順序交換。可積分性が前提であることに注意
example (f : ℝ → ℝ → ℝ)
    (hf : Integrable (Function.uncurry f) (volume.prod volume)) :
    ∫ x : ℝ, ∫ y : ℝ, f x y = ∫ y : ℝ, ∫ x : ℝ, f x y :=
  integral_integral_swap hf
-- BOOK: end fubini-swap

-- BOOK: begin fubini-change
-- 変数変換の公式。ヤコビ行列式の絶対値が体積の伸縮率
#check @MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
-- BOOK: end fubini-change

end Handbook.C24
