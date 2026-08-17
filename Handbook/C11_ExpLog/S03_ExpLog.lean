/- 第11章 指数関数と対数関数
   11.3 exp と自然対数 / 11.4 対数法則 -/
import Mathlib

namespace Handbook.C11

-- BOOK: begin exp-log
-- 指数法則 exp(x+y) = exp x · exp y
example (x y : ℝ) : Real.exp (x + y) = Real.exp x * Real.exp y :=
  Real.exp_add x y

-- exp と log は互いに逆(log は正の実数でだけ本領を発揮する)
example (x : ℝ) : Real.log (Real.exp x) = x := Real.log_exp x

example (x : ℝ) (hx : 0 < x) : Real.exp (Real.log x) = x :=
  Real.exp_log hx
-- BOOK: end exp-log

-- BOOK: begin exp-pos
-- exp の値はつねに正(グラフが x 軸に触れない、の定理版)
example (x : ℝ) : 0 < Real.exp x := Real.exp_pos x
-- BOOK: end exp-pos

-- BOOK: begin exp-e
-- 自然対数の底 e = exp 1 = 2.71828…(小数第9位までの評価が定理)
#check Real.exp_one_gt_d9  -- 2.7182818283 < Real.exp 1
#check Real.exp_one_lt_d9  -- Real.exp 1 < 2.7182818286
-- BOOK: end exp-e

-- BOOK: begin log-laws
-- 対数法則: 積の log は log の和
example (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.log (x * y) = Real.log x + Real.log y :=
  Real.log_mul hx hy
-- BOOK: end log-laws

-- BOOK: begin logb
-- 底 b の対数 logb は自然対数の比(底の変換公式が定義)
example (x : ℝ) :
    Real.logb 10 x = Real.log x / Real.log 10 :=
  rfl
-- BOOK: end logb

-- BOOK: begin logb-eval
-- log₂ 8 = 3。「2 を何乗すれば 8 か」の答え。
example : Real.logb 2 8 = 3 := by
  have h8 : (8 : ℝ) = 2 ^ (3 : ℕ) := by norm_num
  have h2 : Real.log 2 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  rw [Real.logb, h8, Real.log_pow, mul_div_assoc, div_self h2]
  norm_num

-- 対数の商の法則
example (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.log (x / y) = Real.log x - Real.log y :=
  Real.log_div hx hy
-- BOOK: end logb-eval

-- BOOK: begin explog-exercises
-- 演習: 実数乗の計算・指数法則・log の値
example : (2 : ℝ) ^ (3 : ℝ) = 8 := by
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  norm_num

example (x y : ℝ) :
    Real.exp x * Real.exp y = Real.exp (x + y) :=
  (Real.exp_add x y).symm

example : Real.log 1 = 0 := Real.log_one
-- BOOK: end explog-exercises

end Handbook.C11
