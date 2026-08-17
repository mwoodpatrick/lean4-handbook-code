/- 第19章 微分
   19.4 高階微分 / 特別な関数の微分 -/
import Mathlib

namespace Handbook.C19

-- BOOK: begin deriv-special
-- exp は微分しても変わらない唯一の関数(定数倍を除く)
example : deriv Real.exp = Real.exp := by
  funext x
  exact (Real.hasDerivAt_exp x).deriv

-- (sin)' = cos
example : deriv Real.sin = Real.cos := Real.deriv_sin
-- BOOK: end deriv-special

-- BOOK: begin deriv-iterated
-- 高階微分: sin の2階微分は -sin
example (x : ℝ) :
    deriv (deriv Real.sin) x = -Real.sin x := by
  rw [Real.deriv_sin, Real.deriv_cos]
-- BOOK: end deriv-iterated

-- BOOK: begin deriv-exp-char
-- exp は「微分しても自分自身」— 各点でも成り立つ
example (x : ℝ) : deriv Real.exp x = Real.exp x := by
  rw [Real.deriv_exp]

-- (cos)' = -sin
example : deriv Real.cos = fun x => -Real.sin x :=
  Real.deriv_cos'
-- BOOK: end deriv-exp-char

end Handbook.C19
