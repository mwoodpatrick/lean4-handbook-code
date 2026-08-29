/- English edition source: Handbook/C13_Combinatorics/S05_Probability.lean. -/
import Mathlib

namespace Handbook.C13

-- BOOK: begin dice
-- Two dice (stored as faces 0..5; add 1 to read the actual face)
def dice : Finset (ℕ × ℕ) :=
  (Finset.range 6) ×ˢ (Finset.range 6)

-- Outcomes whose faces sum to 7 (sum to 5 in zero-based storage)
def sum7 : Finset (ℕ × ℕ) :=
  dice.filter (fun p => p.1 + p.2 = 5)

#eval dice.card  -- output: 36
#eval sum7.card  -- output: 6
-- BOOK: end dice

-- BOOK: begin dice-prob
-- Classical probability is a ratio of counts. The probability of a sum
-- of 7 is 1/6.
example : (sum7.card : ℚ) / dice.card = 1 / 6 := by
  have h1 : sum7.card = 6 := by decide
  have h2 : dice.card = 36 := by decide
  rw [h1, h2]
  norm_num
-- BOOK: end dice-prob

-- BOOK: begin dice-atleast
-- Count “at least one six” by its complement: 36 − 25 = 11
def hasSix : Finset (ℕ × ℕ) :=
  dice.filter (fun p => p.1 = 5 ∨ p.2 = 5)

example : hasSix.card = 11 := by decide

example : (hasSix.card : ℚ) / dice.card = 11 / 36 := by
  have h : hasSix.card = 11 := by decide
  have h2 : dice.card = 36 := by decide
  rw [h, h2]
  norm_num
-- BOOK: end dice-atleast

-- BOOK: begin expectation
-- Mean (expected value) of a die: (1+2+…+6)/6 = 7/2
#eval ((Finset.range 6).sum (fun k => (k + 1 : ℚ))) / 6
-- output: 7/2

example :
    ((Finset.range 6).sum (fun k => (k + 1 : ℚ))) / 6
      = 7 / 2 := by
  norm_num [Finset.sum_range_succ]
-- BOOK: end expectation

-- BOOK: begin binom-prob
-- Repeated trials: the probability of exactly three heads in five
-- tosses is C(5,3)/2⁵
example : (Nat.choose 5 3 : ℚ) / 2 ^ 5 = 5 / 16 := by
  have h : Nat.choose 5 3 = 10 := by decide
  rw [h]
  norm_num
-- BOOK: end binom-prob

-- BOOK: begin comb-exercises
-- Exercises: binomial coefficients, factorials, and boundary values
example : Nat.choose 6 3 = 20 := by decide

example : Nat.factorial 6 = 720 := by decide

example (n : ℕ) : Nat.choose n 0 = 1 := Nat.choose_zero_right n
-- BOOK: end comb-exercises

end Handbook.C13
