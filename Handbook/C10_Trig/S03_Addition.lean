/- 第10章 三角関数
   10.4 加法定理とその帰結 -/
import Mathlib

namespace Handbook.C10

-- BOOK: begin trig-add
-- 加法定理
example (x y : ℝ) :
    Real.sin (x + y) =
      Real.sin x * Real.cos y + Real.cos x * Real.sin y :=
  Real.sin_add x y

example (x y : ℝ) :
    Real.cos (x + y) =
      Real.cos x * Real.cos y - Real.sin x * Real.sin y :=
  Real.cos_add x y
-- BOOK: end trig-add

-- BOOK: begin trig-double
-- 2倍角の公式は加法定理の系
example (x : ℝ) :
    Real.sin (2 * x) = 2 * Real.sin x * Real.cos x :=
  Real.sin_two_mul x

example (x : ℝ) :
    Real.cos (2 * x) = 2 * Real.cos x ^ 2 - 1 :=
  Real.cos_two_mul x
-- BOOK: end trig-double

-- BOOK: begin trig-supp
-- 例題: 補角の公式 sin(π − x) = sin x を加法定理から導く
example (x : ℝ) : Real.sin (Real.pi - x) = Real.sin x := by
  rw [Real.sin_sub, Real.sin_pi, Real.cos_pi]
  ring

-- mathlib には結論そのものも収録されている
example (x : ℝ) : Real.sin (Real.pi - x) = Real.sin x :=
  Real.sin_pi_sub x
-- BOOK: end trig-supp

-- BOOK: begin trig-halfsq
-- 半角(次数下げ)の公式。積分計算(第20章)の常連。
example (x : ℝ) :
    Real.cos x ^ 2 = 1 / 2 + Real.cos (2 * x) / 2 :=
  Real.cos_sq x
-- BOOK: end trig-halfsq

-- BOOK: begin trig-sumprod
-- 和積の公式: sin の和は積に変わる(うなりの数学)
example (a b : ℝ) :
    Real.sin a + Real.sin b =
      2 * Real.sin ((a + b) / 2) * Real.cos ((a - b) / 2) :=
  Real.sin_add_sin a b
-- BOOK: end trig-sumprod

-- BOOK: begin trig-compose
-- 三角関数の合成: sin x + cos x = √2 sin(x + π/4)
example (x : ℝ) :
    Real.sin x + Real.cos x =
      Real.sqrt 2 * Real.sin (x + Real.pi / 4) := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  rw [Real.sin_add, Real.sin_pi_div_four,
    Real.cos_pi_div_four]
  linear_combination
    (-(Real.sin x + Real.cos x) / 2) * h2
-- BOOK: end trig-compose

-- BOOK: begin trig-exercises
-- 演習: 特別な値・周期性・偶関数
example : Real.cos (Real.pi / 3) = 1 / 2 :=
  Real.cos_pi_div_three

example (x : ℝ) : Real.sin (x + 2 * Real.pi) = Real.sin x :=
  Real.sin_add_two_pi x

example (x : ℝ) : Real.cos (-x) = Real.cos x := Real.cos_neg x
-- BOOK: end trig-exercises

end Handbook.C10
