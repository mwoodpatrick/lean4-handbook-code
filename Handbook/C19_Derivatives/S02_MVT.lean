/- 第19章 微分
   19.3 平均値の定理とその帰結 -/
import Mathlib

namespace Handbook.C19

-- BOOK: begin mvt
-- 平均値の定理: 区間内のどこかで接線の傾き = 平均変化率
example (f f' : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hfc : ContinuousOn f (Set.Icc a b))
    (hff' : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x) :
    ∃ c ∈ Set.Ioo a b, f' c = (f b - f a) / (b - a) :=
  exists_hasDerivAt_eq_slope f f' hab hfc hff'
-- BOOK: end mvt

-- BOOK: begin mvt-mono
-- 帰結: 微分が正なら狭義単調増加
example (f : ℝ → ℝ) (h : ∀ x, 0 < deriv f x) : StrictMono f :=
  strictMono_of_deriv_pos h
-- BOOK: end mvt-mono

-- BOOK: begin rolle
-- ロルの定理: 両端が同じ値なら、途中に f' = 0 の点がある
example (f f' : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hfc : ContinuousOn f (Set.Icc a b))
    (hff' : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hfab : f a = f b) :
    ∃ c ∈ Set.Ioo a b, f' c = 0 :=
  exists_hasDerivAt_eq_zero hab hfc hfab hff'
-- BOOK: end rolle

-- BOOK: begin deriv-const-of
-- 微分が至る所ゼロなら定数(平均値の定理の帰結)
example (f : ℝ → ℝ) (hd : Differentiable ℝ f)
    (h : ∀ x, deriv f x = 0) : ∀ x y, f x = f y :=
  is_const_of_deriv_eq_zero hd h
-- BOOK: end deriv-const-of

end Handbook.C19
