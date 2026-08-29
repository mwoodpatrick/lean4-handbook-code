/- English edition source: Handbook/C33_Measure/S06_Lp.lean. -/
import Mathlib

namespace Handbook.C33

open MeasureTheory Filter

-- BOOK: begin lp-space
-- L² is the stage on which Hilbert spaces live (Chapter 34)
example : CompleteSpace (Lp ℝ 2 (volume : Measure ℝ)) := by
  infer_instance

-- L¹ is a Banach space too
example : CompleteSpace (Lp ℝ 1 (volume : Measure ℝ)) := by
  infer_instance
-- BOOK: end lp-space

-- BOOK: begin holder
-- Hölder's inequality: it splits a product when 1/p + 1/q = 1
example (α : Type) [MeasurableSpace α] (μ : Measure α) (p q : ℝ)
    (hpq : p.HolderConjugate q) (f g : α → ENNReal)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ a, (f * g) a ∂μ
      ≤ (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) * (∫⁻ a, g a ^ q ∂μ) ^ (1 / q) :=
  ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf hg
-- BOOK: end holder

-- BOOK: begin strong-law
-- The strong law of large numbers: for independent, identically
-- distributed variables the sample mean converges to the mean
example (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (hint : Integrable (X 0) μ)
    (hindep : Pairwise
      (Function.onFun (fun a b => ProbabilityTheory.IndepFun a b μ) X))
    (hid : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω)
      atTop (nhds (∫ x, X 0 x ∂μ)) :=
  ProbabilityTheory.strong_law_ae X hint hindep hid
-- BOOK: end strong-law

end Handbook.C33
