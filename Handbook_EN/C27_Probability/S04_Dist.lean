/- English edition source: Handbook/C27_Probability/S04_Dist.lean. -/
import Mathlib

namespace Handbook.C27

open MeasureTheory ProbabilityTheory

-- BOOK: begin dist-map
-- The distribution of a random variable X is the pushforward along X.
-- Forget what Ω was and look only at the measure on the value space.
#check @MeasureTheory.Measure.map

example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (hX : Measurable X) (s : Set ℝ)
    (hs : MeasurableSet s) :
    (μ.map X) s = μ (X ⁻¹' s) :=
  Measure.map_apply hX hs
-- BOOK: end dist-map

-- BOOK: begin dist-uniform
-- Uniform distribution on a finite type: every value has equal
-- probability.
noncomputable def die : PMF (Fin 6) :=
  PMF.uniformOfFintype (Fin 6)

example : die 0 = 1 / 6 := by
  simp [die, PMF.uniformOfFintype_apply]
-- BOOK: end dist-uniform

-- BOOK: begin dist-gauss
-- The normal distribution is defined as a measure
#check @ProbabilityTheory.gaussianReal

-- the exponential and Bernoulli distributions
#check @ProbabilityTheory.exponentialPDF
#check @ProbabilityTheory.bernoulliMeasure
-- BOOK: end dist-gauss

end Handbook.C27
