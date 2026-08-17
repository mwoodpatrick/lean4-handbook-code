/- 第10章 三角関数
   10.6 三角方程式 -/
import Mathlib

namespace Handbook.C10

open Real

-- BOOK: begin trig-eq
-- sin x = 0 の解は x = nπ(整数 n)で尽きる
example (x : ℝ) :
    Real.sin x = 0 ↔ ∃ n : ℤ, (n : ℝ) * π = x :=
  Real.sin_eq_zero_iff
-- BOOK: end trig-eq

-- BOOK: begin trig-eq-cos
-- cos x = 1 の解は x = 2nπ
example (x : ℝ) :
    Real.cos x = 1 ↔ ∃ n : ℤ, (n : ℝ) * (2 * π) = x :=
  Real.cos_eq_one_iff x
-- BOOK: end trig-eq-cos

end Handbook.C10
