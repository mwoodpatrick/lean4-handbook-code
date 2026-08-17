/- 第10章 三角関数
   10.3 基本恒等式 -/
import Mathlib

namespace Handbook.C10

-- BOOK: begin trig-sq
-- 単位円の方程式 sin²x + cos²x = 1
example (x : ℝ) : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 :=
  Real.sin_sq_add_cos_sq x
-- BOOK: end trig-sq

-- BOOK: begin trig-bound
-- したがって sin も cos も [-1, 1] に収まる
example (x : ℝ) : |Real.sin x| ≤ 1 := Real.abs_sin_le_one x
example (x : ℝ) : Real.cos x ≤ 1 := Real.cos_le_one x
-- BOOK: end trig-bound

-- BOOK: begin trig-cos-from-sin
-- 例題: cos²x = 1 − sin²x(単位円の方程式の言い換え)
example (x : ℝ) :
    Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
  have h := Real.sin_sq_add_cos_sq x
  linarith
-- BOOK: end trig-cos-from-sin

end Handbook.C10
