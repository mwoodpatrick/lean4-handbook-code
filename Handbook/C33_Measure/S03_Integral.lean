/- 第33章 測度論とルベーグ積分
   33.4 ルベーグ積分の構成 -/
import Mathlib

namespace Handbook.C33

open MeasureTheory

-- BOOK: begin lintegral-indicator
-- 単関数の原型: 指示関数の積分は「集合の上での積分」に等しい
example (α : Type) [MeasurableSpace α] (μ : Measure α) (s : Set α)
    (hs : MeasurableSet s) (f : α → ENNReal) :
    ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f a ∂μ :=
  lintegral_indicator hs f
-- BOOK: end lintegral-indicator

-- BOOK: begin integral-basic
-- 定数関数の積分は「定数 × 全体の測度」
example (α : Type) [MeasurableSpace α] (μ : Measure α) (c : ℝ) :
    ∫ _x, c ∂μ = μ.real Set.univ • c :=
  integral_const c

-- 積分の線形性。可積分性の仮定が両方に要る
example (α : Type) [MeasurableSpace α] (μ : Measure α)
    (f g : α → ℝ) (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ a, (f a + g a) ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ :=
  integral_add hf hg
-- BOOK: end integral-basic

-- BOOK: begin integral-mono
-- 積分の単調性。大小関係は積分を通しても保たれる
example (α : Type) [MeasurableSpace α] (μ : Measure α)
    (f g : α → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hle : f ≤ g) : ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ :=
  integral_mono hf hg hle

-- 三角不等式の積分版。絶対値を外へ出すと大きくなる
example (α : Type) [MeasurableSpace α] (μ : Measure α)
    (f : α → ℝ) : ‖∫ a, f a ∂μ‖ ≤ ∫ a, ‖f a‖ ∂μ :=
  norm_integral_le_integral_norm f
-- BOOK: end integral-mono

-- BOOK: begin integral-interval
-- 第20章の区間積分はルベーグ積分の特別な場合である
example : ∫ _x in (0 : ℝ)..1, (2 : ℝ) = 2 := by
  simp
-- BOOK: end integral-interval

end Handbook.C33
