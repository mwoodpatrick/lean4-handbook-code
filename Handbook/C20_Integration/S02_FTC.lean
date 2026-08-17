/- 第20章 積分
   20.3 微積分学の基本定理 / 20.4 置換積分と部分積分 -/
import Mathlib

namespace Handbook.C20

open intervalIntegral MeasureTheory

-- BOOK: begin ftc
-- 微積分学の基本定理: 導関数を積分すると元の関数の差になる
example (f f' : ℝ → ℝ) (a b : ℝ)
    (h : ∀ x ∈ Set.uIcc a b, HasDerivAt f (f' x) x)
    (h' : IntervalIntegrable f' volume a b) :
    ∫ x in a..b, f' x = f b - f a :=
  integral_eq_sub_of_hasDerivAt h h'
-- BOOK: end ftc

-- BOOK: begin byparts
-- 部分積分の一般形(mathlib の宣言を確認する)
#check @intervalIntegral.integral_mul_deriv_eq_deriv_mul
-- BOOK: end byparts

-- BOOK: begin ftc-apply
-- FTC の応用: 導関数 f' の積分は端点での f の差になる
-- (原始関数 F を与えれば ∫ F' = F b - F a)
example (F : ℝ → ℝ) (a b : ℝ)
    (hdiff : ∀ x ∈ Set.uIcc a b, DifferentiableAt ℝ F x)
    (hint : IntervalIntegrable (deriv F) volume a b) :
    ∫ x in a..b, deriv F x = F b - F a :=
  integral_deriv_eq_sub hdiff hint
-- BOOK: end ftc-apply

end Handbook.C20
