/- 第25章 微分方程式
   25.3 求積法 — 解いてから検算する -/
import Mathlib

namespace Handbook.C25

-- BOOK: begin solve-separable
-- 変数分離形 ẋ = 2t·x の解 x(t) = C·e^{t²} を検算する
example (C t : ℝ) :
    HasDerivAt (fun s : ℝ => C * Real.exp (s ^ 2))
      (2 * t * (C * Real.exp (t ^ 2))) t := by
  have h : HasDerivAt (fun s : ℝ => Real.exp (s ^ 2))
      (Real.exp (t ^ 2) * (2 * t)) t := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (t ^ 2)).comp t (hasDerivAt_pow 2 t)
  have := h.const_mul C
  simpa [mul_comm, mul_assoc, mul_left_comm] using this
-- BOOK: end solve-separable

-- BOOK: begin solve-linear
-- 1階線形 ẋ = -x + 1 の解 x(t) = 1 + C·e^{-t}
example (C t : ℝ) :
    HasDerivAt (fun s : ℝ => 1 + C * Real.exp (-s))
      (-(1 + C * Real.exp (-t)) + 1) t := by
  have h : HasDerivAt (fun s : ℝ => Real.exp (-s))
      (-Real.exp (-t)) t := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)
  have := (h.const_mul C).const_add 1
  simpa [mul_comm] using this
-- BOOK: end solve-linear

-- BOOK: begin solve-ivp
-- 初期条件 x(0) = x₀ が積分定数 C を決める。
-- 一般解の族から1本を選び出すのが初期値問題である
example (x₀ : ℝ) : (fun s : ℝ => x₀ * Real.exp s) 0 = x₀ := by
  simp
-- BOOK: end solve-ivp

end Handbook.C25
