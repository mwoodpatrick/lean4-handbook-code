/- English edition source: Handbook/C33_Measure/S05_Fubini.lean. -/
import Mathlib

namespace Handbook.C33

open MeasureTheory

-- BOOK: begin fubini
-- Fubini: the multiple integral equals the iterated one;
-- integrability has to be assumed
example (α β : Type) [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (f : α × β → ℝ) (hf : Integrable f (μ.prod ν)) :
    ∫ z, f z ∂μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ :=
  integral_prod f hf
-- BOOK: end fubini

-- BOOK: begin fubini-tonelli
-- Tonelli’s theorem: nonnegative functions permit exchanging the order
-- without assuming integrability.
example (α β : Type) [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (f : α × β → ENNReal) (hf : Measurable f) :
    ∫⁻ z, f z ∂μ.prod ν = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ :=
  lintegral_prod f hf.aemeasurable
-- BOOK: end fubini-tonelli

end Handbook.C33
