/- 第33章 測度論とルベーグ積分
   33.6 Fubini の定理 -/
import Mathlib

namespace Handbook.C33

open MeasureTheory

-- BOOK: begin fubini
-- Fubini: 重積分は累次積分に等しい。可積分性が仮定に要る
example (α β : Type) [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (f : α × β → ℝ) (hf : Integrable f (μ.prod ν)) :
    ∫ z, f z ∂μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ :=
  integral_prod f hf
-- BOOK: end fubini

-- BOOK: begin fubini-tonelli
-- Tonelli: 非負関数なら可積分性を仮定せずに交換してよい
example (α β : Type) [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (f : α × β → ENNReal) (hf : Measurable f) :
    ∫⁻ z, f z ∂μ.prod ν = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ :=
  lintegral_prod f hf.aemeasurable
-- BOOK: end fubini-tonelli

end Handbook.C33
