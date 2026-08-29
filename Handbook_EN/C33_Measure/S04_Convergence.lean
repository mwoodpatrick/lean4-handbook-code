/- English edition source: Handbook/C33_Measure/S04_Convergence.lean. -/
import Mathlib

namespace Handbook.C33

open MeasureTheory Filter

-- BOOK: begin monotone-conv
-- Monotone convergence theorem: for an increasing sequence, supremum
-- and integral can be interchanged.
example (α : Type) [MeasurableSpace α] (μ : Measure α)
    (f : ℕ → α → ENNReal) (hm : ∀ n, Measurable (f n))
    (hmono : Monotone f) :
    ∫⁻ a, ⨆ n, f n a ∂μ = ⨆ n, ∫⁻ a, f n a ∂μ :=
  lintegral_iSup hm hmono
-- BOOK: end monotone-conv

-- BOOK: begin dominated-conv
-- Dominated convergence: given an integrable dominating function,
-- the limit and the integral may be exchanged
example (α : Type) [MeasurableSpace α] (μ : Measure α)
    (F : ℕ → α → ℝ) (f : α → ℝ) (bound : α → ℝ)
    (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hb : Integrable bound μ)
    (hle : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a)
    (hlim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (nhds (f a))) :
    Tendsto (fun n => ∫ a, F n a ∂μ) atTop (nhds (∫ a, f a ∂μ)) :=
  tendsto_integral_of_dominated_convergence bound hF hb hle hlim
-- BOOK: end dominated-conv

-- BOOK: begin fatou
-- Fatou's lemma: a one-sided inequality that needs no hypotheses
example (α : Type) [MeasurableSpace α] (μ : Measure α)
    (f : ℕ → α → ENNReal) (hm : ∀ n, Measurable (f n)) :
    ∫⁻ a, liminf (fun n => f n a) atTop ∂μ
      ≤ liminf (fun n => ∫⁻ a, f n a ∂μ) atTop :=
  lintegral_liminf_le hm
-- BOOK: end fatou

end Handbook.C33
