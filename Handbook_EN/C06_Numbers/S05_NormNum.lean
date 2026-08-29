/- English edition source: Handbook/C06_Numbers/S05_NormNum.lean. -/
import Mathlib

namespace Handbook.C06

-- BOOK: begin nn-intro
-- The claim from the start of this chapter. Not the output of a
-- calculator but a checked theorem.
example : 999 * 1001 = 999999 := by norm_num

example : (1 : ℚ) / 7 < 1 / 6 := by norm_num
example : 2 ^ 10 = 1024 := by norm_num
-- BOOK: end nn-intro

-- BOOK: begin nn-basic
example : (123 : ℕ) * 321 = 39483 := by norm_num

example : (2 : ℚ) / 3 + 1 / 6 = 5 / 6 := by norm_num

-- norm_num has an extension for primality testing
example : Nat.Prime 2027 := by norm_num
-- BOOK: end nn-basic

-- BOOK: begin nn-decide
-- For a small divisibility claim, decide's exhaustive check will do
example : 3 ∣ 111 := by decide
example : ¬ 7 ∣ 100 := by decide
-- BOOK: end nn-decide

-- BOOK: begin numbers-exercises
-- Exercises: three problems with this chapter's tools
-- (ring, norm_num, the lemmas on absolute values)
example (x : ℚ) : (x + 5) ^ 2 - (x - 5) ^ 2 = 20 * x := by
  ring

example : Nat.Prime 101 := by norm_num

example (a : ℚ) (h : |a| < 2) : -2 < a := (abs_lt.mp h).1
-- BOOK: end numbers-exercises

end Handbook.C06
