/- Chapter 11: Exponential and logarithmic functions
   11.6 Increase, decrease, and graphs -/
import Mathlib

namespace Handbook.C11

-- BOOK: begin exp-mono
-- exp is strictly monotone increasing and always positive
example : StrictMono Real.exp := Real.exp_strictMono
example (x : ℝ) : 0 < Real.exp x := Real.exp_pos x
-- BOOK: end exp-mono

-- BOOK: begin log-mono
-- log is strictly monotone increasing on the positive reals
example : StrictMonoOn Real.log (Set.Ioi 0) :=
  Real.strictMonoOn_log
-- BOOK: end log-mono

-- BOOK: begin exp-eq
-- Exponential equations and inequalities drop, by injectivity and
-- monotonicity, to a comparison of exponents
example (x : ℝ) : Real.exp x = Real.exp 3 ↔ x = 3 :=
  Real.exp_eq_exp

example (x y : ℝ) : Real.exp x < Real.exp y ↔ x < y :=
  Real.exp_lt_exp
-- BOOK: end exp-eq

-- BOOK: begin exp-solve
-- Worked example: solve e^(2x) = e^(x+1)
example (x : ℝ) :
    Real.exp (2 * x) = Real.exp (x + 1)
      ↔ x = 1 := by
  rw [Real.exp_eq_exp]
  constructor
  · intro h; linarith
  · rintro rfl; norm_num
-- BOOK: end exp-solve

-- BOOK: begin log-solve
-- The sign of a logarithm is decided by comparison with 1
example (x : ℝ) (hx : 0 < x) : Real.log x < 0 ↔ x < 1 :=
  Real.log_neg_iff hx

example (x : ℝ) (hx : 1 < x) : 0 < Real.log x :=
  Real.log_pos hx
-- BOOK: end log-solve

end Handbook.C11
