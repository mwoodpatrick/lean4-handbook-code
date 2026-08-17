/- 第27章 確率論の基礎
   27.3 確率変数と分布 / 27.6 主要な分布 -/
import Mathlib

namespace Handbook.C27

open MeasureTheory ProbabilityTheory

-- BOOK: begin dist-map
-- 確率変数 X の分布とは、測度を X で押し出したもの。
-- Ω が何であったかを忘れ、値の空間の上の測度だけを見る
#check @MeasureTheory.Measure.map

example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (hX : Measurable X) (s : Set ℝ)
    (hs : MeasurableSet s) :
    (μ.map X) s = μ (X ⁻¹' s) :=
  Measure.map_apply hX hs
-- BOOK: end dist-map

-- BOOK: begin dist-uniform
-- 有限型の一様分布。すべての値が等確率
noncomputable def die : PMF (Fin 6) :=
  PMF.uniformOfFintype (Fin 6)

example : die 0 = 1 / 6 := by
  simp [die, PMF.uniformOfFintype_apply]
-- BOOK: end dist-uniform

-- BOOK: begin dist-gauss
-- 正規分布(ガウス分布)は測度として定義されている
#check @ProbabilityTheory.gaussianReal

-- 指数分布・ベルヌーイ分布も同様
#check @ProbabilityTheory.exponentialPDF
#check @ProbabilityTheory.bernoulliMeasure
-- BOOK: end dist-gauss

end Handbook.C27
