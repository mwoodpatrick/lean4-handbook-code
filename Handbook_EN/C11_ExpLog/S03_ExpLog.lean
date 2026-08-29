/- English edition source: Handbook/C11_ExpLog/S03_ExpLog.lean. -/
import Mathlib

namespace Handbook.C11

-- BOOK: begin exp-log
-- Exponential law: exp(x+y) = exp x · exp y
example (x y : ℝ) : Real.exp (x + y) = Real.exp x * Real.exp y :=
  Real.exp_add x y

-- exp and log are inverses (log behaves as intended on positive reals)
example (x : ℝ) : Real.log (Real.exp x) = x := Real.log_exp x

example (x : ℝ) (hx : 0 < x) : Real.exp (Real.log x) = x :=
  Real.exp_log hx
-- BOOK: end exp-log

-- BOOK: begin exp-pos
-- exp is always positive (the theorem-level version of its graph never
-- touching the x-axis)
example (x : ℝ) : 0 < Real.exp x := Real.exp_pos x
-- BOOK: end exp-pos

-- BOOK: begin exp-e
-- The base of the natural logarithm e = exp 1 = 2.71828… (a theorem
-- bounds it to nine decimal places)
#check Real.exp_one_gt_d9  -- 2.7182818283 < Real.exp 1
#check Real.exp_one_lt_d9  -- Real.exp 1 < 2.7182818286
-- BOOK: end exp-e

-- BOOK: begin log-laws
-- Logarithm law: the log of a product is the sum of the logs
example (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.log (x * y) = Real.log x + Real.log y :=
  Real.log_mul hx hy
-- BOOK: end log-laws

-- BOOK: begin logb
-- The base-b logarithm logb is a ratio of natural logs (change of base
-- is the definition)
example (x : ℝ) :
    Real.logb 10 x = Real.log x / Real.log 10 :=
  rfl
-- BOOK: end logb

-- BOOK: begin logb-eval
-- log₂ 8 = 3: the answer to "to what power must 2 be raised to obtain
-- 8?"
example : Real.logb 2 8 = 3 := by
  have h8 : (8 : ℝ) = 2 ^ (3 : ℕ) := by norm_num
  have h2 : Real.log 2 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  rw [Real.logb, h8, Real.log_pow, mul_div_assoc, div_self h2]
  norm_num

-- Quotient law for logarithms
example (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.log (x / y) = Real.log x - Real.log y :=
  Real.log_div hx hy
-- BOOK: end logb-eval

-- BOOK: begin explog-exercises
-- Exercises: computations with real powers, exponential laws, and
-- values of log
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
