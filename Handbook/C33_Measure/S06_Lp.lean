/- 第33章 測度論とルベーグ積分
   33.7 Lᵖ 空間 / 33.8 大数の強法則 -/
import Mathlib

namespace Handbook.C33

open MeasureTheory Filter

-- BOOK: begin lp-space
-- L² は完備。これが Hilbert 空間論(第34章)の主要な舞台になる
example : CompleteSpace (Lp ℝ 2 (volume : Measure ℝ)) := by
  infer_instance

-- L¹ も Banach 空間である
example : CompleteSpace (Lp ℝ 1 (volume : Measure ℝ)) := by
  infer_instance
-- BOOK: end lp-space

-- BOOK: begin holder
-- Hölder の不等式。1/p + 1/q = 1 のとき積の積分を分離できる
example (α : Type) [MeasurableSpace α] (μ : Measure α) (p q : ℝ)
    (hpq : p.HolderConjugate q) (f g : α → ENNReal)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ a, (f * g) a ∂μ
      ≤ (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) * (∫⁻ a, g a ^ q ∂μ) ^ (1 / q) :=
  ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf hg
-- BOOK: end holder

-- BOOK: begin strong-law
-- 大数の強法則: 独立同分布なら標本平均が期待値へ概収束する
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
