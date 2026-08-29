/- English edition source: Handbook/C10_Trig/S02_Identities.lean. -/
import Mathlib

namespace Handbook.C10

-- BOOK: begin trig-sq
-- The unit-circle equation sin²x + cos²x = 1
example (x : ℝ) : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 :=
  Real.sin_sq_add_cos_sq x
-- BOOK: end trig-sq

-- BOOK: begin trig-bound
-- hence both sin and cos stay inside [-1, 1]
example (x : ℝ) : |Real.sin x| ≤ 1 := Real.abs_sin_le_one x
example (x : ℝ) : Real.cos x ≤ 1 := Real.cos_le_one x
-- BOOK: end trig-bound

-- BOOK: begin trig-cos-from-sin
-- Example: cos²x = 1 − sin²x (a restatement of the unit-circle
-- equation)
example (x : ℝ) :
    Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
  have h := Real.sin_sq_add_cos_sq x
  linarith
-- BOOK: end trig-cos-from-sin

end Handbook.C10
