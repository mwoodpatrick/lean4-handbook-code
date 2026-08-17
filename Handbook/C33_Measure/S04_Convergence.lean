/- 第33章 測度論とルベーグ積分
   33.5 収束定理 -/
import Mathlib

namespace Handbook.C33

open MeasureTheory Filter

-- BOOK: begin monotone-conv
-- 単調収束定理: 増加列なら sup と積分が交換できる
example (α : Type) [MeasurableSpace α] (μ : Measure α)
    (f : ℕ → α → ENNReal) (hm : ∀ n, Measurable (f n))
    (hmono : Monotone f) :
    ∫⁻ a, ⨆ n, f n a ∂μ = ⨆ n, ∫⁻ a, f n a ∂μ :=
  lintegral_iSup hm hmono
-- BOOK: end monotone-conv

-- BOOK: begin dominated-conv
-- 優収束定理: 可積分な「傘」があれば極限と積分を交換できる
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
-- Fatou の補題: 単調性も傘もなしで、片側の不等式だけは常に成り立つ
example (α : Type) [MeasurableSpace α] (μ : Measure α)
    (f : ℕ → α → ENNReal) (hm : ∀ n, Measurable (f n)) :
    ∫⁻ a, liminf (fun n => f n a) atTop ∂μ
      ≤ liminf (fun n => ∫⁻ a, f n a ∂μ) atTop :=
  lintegral_liminf_le hm
-- BOOK: end fatou

end Handbook.C33
