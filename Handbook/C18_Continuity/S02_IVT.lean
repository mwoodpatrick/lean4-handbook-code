/- 第18章 関数の極限と連続性
   18.3 中間値の定理 -/
import Mathlib

namespace Handbook.C18

-- BOOK: begin ivt
-- 中間値の定理: 符号が変われば零点がある
example (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1))
    (h0 : f 0 < 0) (h1 : 0 < f 1) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, f x = 0 := by
  have himg := intermediate_value_Icc
    (by norm_num : (0 : ℝ) ≤ 1) hf
  have h : (0 : ℝ) ∈ Set.Icc (f 0) (f 1) := by
    constructor <;> linarith
  obtain ⟨x, hx, hfx⟩ := himg h
  exact ⟨x, hx, hfx⟩
-- BOOK: end ivt

end Handbook.C18
