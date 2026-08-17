/- 第20章 積分
   20.6 置換積分と広義積分 -/
import Mathlib

namespace Handbook.C20

open intervalIntegral MeasureTheory

-- BOOK: begin substitution
-- 置換積分。合成の微分(連鎖律)を逆にたどったもの
#check @intervalIntegral.integral_deriv_smul_comp
-- BOOK: end substitution

-- BOOK: begin log-integral
-- 1/x の積分が対数になる。原始関数が初等関数で書ける例
example {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x in a..b, 1 / x = Real.log (b / a) :=
  integral_one_div_of_pos ha hb
-- BOOK: end log-integral

-- BOOK: begin improper
-- 無限区間の積分。区間積分の極限として基本定理を延ばす
#check @MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto

-- x^p の可積分性が p の値で決まる
#check @integrableOn_Ioi_rpow_iff
-- BOOK: end improper

-- BOOK: begin integrable-on
-- 可積分性は述語。積分値が有限であることを別に言う必要がある
#check @MeasureTheory.IntegrableOn
#check @IntervalIntegrable
-- BOOK: end integrable-on

end Handbook.C20
