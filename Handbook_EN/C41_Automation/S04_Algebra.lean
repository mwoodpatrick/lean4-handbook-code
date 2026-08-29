/- English edition source: Handbook/C41_Automation/S04_Algebra.lean. -/
import Mathlib

namespace Handbook.C41

-- BOOK: begin ring
-- ring: proves equalities in commutative rings; variables are allowed,
-- but the goal must be an equality.
example (x : ℚ) : x ^ 2 - 1 = (x - 1) * (x + 1) := by ring
example (R : Type) [CommRing R] (a b : R) :
    (a + b) ^ 3 = a ^ 3 + 3 * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3 := by
  ring
-- BOOK: end ring

-- BOOK: begin linarith
-- linarith: linear inequalities, deriving a contradiction from a
-- linear combination of the hypotheses
example (x y : ℝ) (h1 : x ≤ 3) (h2 : y ≤ 2) : x + y ≤ 5 := by
  linarith

-- nlinarith handles nonlinear goals too; hand it auxiliary terms
-- as hints
example (x : ℝ) : 0 ≤ x ^ 2 + 2 * x + 1 := by
  nlinarith [sq_nonneg (x + 1)]
-- BOOK: end linarith

-- BOOK: begin positivity
-- positivity: decides "obviously positive or nonnegative" from the
-- syntax
example (x : ℝ) (hx : 0 < x) : 0 < x ^ 2 + Real.exp x := by
  positivity

example (x : ℝ) : 0 ≤ |x| + x ^ 2 := by positivity
-- BOOK: end positivity

-- BOOK: begin gcongr
-- gcongr: rewrite one part of an inequality using monotonicity
example (a b c : ℝ) (h : a ≤ b) (hc : 0 ≤ c) :
    a * c ≤ b * c := by
  gcongr

example (a b : ℝ) (h : a ≤ b) : a + 5 ≤ b + 5 := by gcongr
-- BOOK: end gcongr

end Handbook.C41
