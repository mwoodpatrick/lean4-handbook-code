/- English edition source: Handbook/C33_Measure/S03_Integral.lean. -/
import Mathlib

namespace Handbook.C33

open MeasureTheory

-- BOOK: begin lintegral-indicator
-- Prototype of a simple function: the integral of an indicator equals
-- the integral over the set.
example (α : Type) [MeasurableSpace α] (μ : Measure α) (s : Set α)
    (hs : MeasurableSet s) (f : α → ENNReal) :
    ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f a ∂μ :=
  lintegral_indicator hs f
-- BOOK: end lintegral-indicator

-- BOOK: begin integral-basic
-- The integral of a constant function is “constant value × total
-- measure.”
example (α : Type) [MeasurableSpace α] (μ : Measure α) (c : ℝ) :
    ∫ _x, c ∂μ = μ.real Set.univ • c :=
  integral_const c

-- Linearity of the integral, with integrability assumed on both sides
example (α : Type) [MeasurableSpace α] (μ : Measure α)
    (f g : α → ℝ) (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ a, (f a + g a) ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ :=
  integral_add hf hg
-- BOOK: end integral-basic

-- BOOK: begin integral-mono
-- Monotonicity of the integral: inequalities are preserved by
-- integration.
example (α : Type) [MeasurableSpace α] (μ : Measure α)
    (f g : α → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hle : f ≤ g) : ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ :=
  integral_mono hf hg hle

-- The triangle inequality for integrals: taking absolute values
-- inside only makes it larger
example (α : Type) [MeasurableSpace α] (μ : Measure α)
    (f : α → ℝ) : ‖∫ a, f a ∂μ‖ ≤ ∫ a, ‖f a‖ ∂μ :=
  norm_integral_le_integral_norm f
-- BOOK: end integral-mono

-- BOOK: begin integral-interval
-- The interval integral of Chapter 20 is a special case of the
-- Lebesgue integral
example : ∫ _x in (0 : ℝ)..1, (2 : ℝ) = 2 := by
  simp
-- BOOK: end integral-interval

end Handbook.C33
