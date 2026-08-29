/- English edition source: Handbook/AppA_Tactics/A02_Arith.lean. -/
import Mathlib

namespace Handbook.AppA

-- BOOK: begin t-ring
-- ring: normalize an equality in a commutative ring and close it
example (a b : ℤ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring
-- BOOK: end t-ring

-- BOOK: begin t-linarith
-- linarith: linear inequalities; combines hypotheses linearly to derive
-- a contradiction
example (x y : ℝ) (h1 : x ≤ 3) (h2 : y ≤ 2) : x + y ≤ 5 := by
  linarith
-- BOOK: end t-linarith

-- BOOK: begin t-nlinarith
-- nlinarith: nonlinear; you add facts such as nonnegativity of squares
-- yourself
example (x : ℝ) : 0 ≤ x ^ 2 + 2 * x + 1 := by
  nlinarith [sq_nonneg (x + 1)]
-- BOOK: end t-nlinarith

-- BOOK: begin t-norm-num
-- norm_num: numeric computation, comparison, and primality testing
example : (2 : ℝ) + 2 = 4 := by norm_num

example : Nat.Prime 101 := by norm_num
-- BOOK: end t-norm-num

-- BOOK: begin t-omega
-- omega: linear arithmetic over ℕ and ℤ; handles subtraction and
-- remainder too
example (n : ℕ) (h : n > 3) : n - 1 > 2 := by omega

example (a b : ℤ) (h : 2 * a + 3 * b = 7) (h2 : a = 2) : b = 1 := by
  omega
-- BOOK: end t-omega

-- BOOK: begin t-positivity
-- positivity: decide positivity, nonnegativity, and nonzeroness from
-- the syntax
example (x : ℝ) (hx : 0 < x) : 0 < x ^ 2 + x := by positivity

example (x : ℝ) : 0 ≤ x ^ 2 + 1 := by positivity
-- BOOK: end t-positivity

-- BOOK: begin t-field-simp
-- field_simp: clear denominators; requires that the denominators are
-- nonzero
example (x : ℝ) (hx : x ≠ 0) : 1 / x + 1 = (1 + x) / x := by
  field_simp
-- BOOK: end t-field-simp

-- BOOK: begin t-linear-combination
-- linear_combination: build the goal equality from a linear combination
-- of hypotheses
example (x y : ℝ) (h1 : x + y = 3) (h2 : x - y = 1) : x = 2 := by
  linear_combination (h1 + h2) / 2
-- BOOK: end t-linear-combination

-- BOOK: begin t-gcongr
-- gcongr: compare only the corresponding parts of an inequality
example (a b c : ℝ) (h : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b := by
  gcongr
-- BOOK: end t-gcongr

-- BOOK: begin t-decide
-- decide: close a decidable proposition by exhaustive check
example : (7 : ℕ) ∣ 91 := by decide

example : ∀ n : Fin 5, n.val < 5 := by decide
-- BOOK: end t-decide

-- BOOK: begin t-simp
-- simp: apply simplification rules repeatedly; only restricts to the
-- given rules
example (l : List ℕ) : (l ++ []).length = l.length := by simp

example (a : ℕ) : a + 0 = a := by simp only [Nat.add_zero]
-- BOOK: end t-simp

-- BOOK: begin t-cast
-- push_cast / exact_mod_cast: move coercions (↑) around to line things
-- up
example (n : ℕ) : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by
  push_cast
  ring

example (n : ℕ) (h : (n : ℤ) = 3) : n = 3 := by
  exact_mod_cast h
-- BOOK: end t-cast

end Handbook.AppA
