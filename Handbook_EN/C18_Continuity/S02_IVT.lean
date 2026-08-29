/- English edition source: Handbook/C18_Continuity/S02_IVT.lean. -/
import Mathlib

namespace Handbook.C18

-- BOOK: begin ivt
-- Intermediate value theorem: a sign change forces a zero
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
