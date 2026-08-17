/- 第27章 確率論の基礎
   27.4 条件つき確率と独立性 -/
import Mathlib

namespace Handbook.C27

open MeasureTheory ProbabilityTheory

-- BOOK: begin cond-def
-- 条件つき確率 μ[t | s] は「s に制限して測り直した測度」。
-- 定義は P(s ∩ t) / P(s) そのもの
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    {s : Set Ω} (hs : MeasurableSet s) (t : Set Ω) :
    μ[t | s] = (μ s)⁻¹ * μ (s ∩ t) :=
  ProbabilityTheory.cond_apply hs μ t
-- BOOK: end cond-def

-- BOOK: begin cond-chain
-- 乗法定理 P(s) · P(t|s) = P(s ∩ t)。
-- 条件つき確率の定義を分母を払って書き直したもの
#check @ProbabilityTheory.cond_mul_eq_inter

-- 条件を重ねると共通部分の条件に等しい
#check @ProbabilityTheory.cond_cond_eq_cond_inter
-- BOOK: end cond-chain

-- BOOK: begin indep-def
-- 独立性: 2つの事象・2つの確率変数それぞれに定義がある
#check @ProbabilityTheory.IndepSet
#check @ProbabilityTheory.IndepFun

-- 3つ以上は「どの有限部分族についても積になる」。
-- 2つずつの独立性より強い条件である
#check @ProbabilityTheory.iIndepFun
-- BOOK: end indep-def

end Handbook.C27
