/- Chapter 6: Numbers and expressions
   6.1 The number systems and coercion -/
import Mathlib

namespace Handbook.C06

-- BOOK: begin num-coe
-- Using the natural number 3 as an integer inserts the coercion ↑
#check ((3 : ℕ) : ℤ)  -- ↑3 : ℤ

-- for a computation crossing a coercion, tidy inward with push_cast
-- and then call ring
example (n : ℕ) : ((n + 1 : ℕ) : ℚ) = n + 1 := by
  push_cast
  ring
-- BOOK: end num-coe

-- BOOK: begin num-castdown
-- The other direction (from an equation in ℚ to one in ℕ)
-- is exact_mod_cast
example (a b : ℕ) (h : (a : ℚ) = b) : a = b := by
  exact_mod_cast h
-- BOOK: end num-castdown

-- BOOK: begin num-why-z
-- Subtraction, which truncates in ℕ, becomes free once we move up to ℤ
example (n : ℕ) : (n : ℤ) - (n + 1 : ℕ) = -1 := by
  push_cast
  ring

-- the -3 of ℤ has no image in ℕ
-- (a demonstration of "there is no bridge leftwards")
example : ¬ ∃ n : ℕ, (n : ℤ) = -3 := by
  rintro ⟨n, hn⟩
  omega
-- BOOK: end num-why-z

-- BOOK: begin num-digits
-- Positional notation: 45 written in binary is 101101
-- output: [1, 0, 1, 1, 0, 1] (from the lowest digit)
#eval Nat.digits 2 45
#eval Nat.digits 10 45  -- output: [5, 4]

-- the number is recovered from its list of digits (checked by decide)
example : Nat.ofDigits 2 [1, 0, 1, 1, 0, 1] = 45 := by decide
-- BOOK: end num-digits

-- BOOK: begin num-decimal
-- The decimal expansion of a rational always repeats.
-- The repeating block of 1/7 is 142857.
#eval (10 ^ 6 / 7 : ℕ)  -- output: 142857
#eval 142857 * 7        -- output: 999999 (= 10⁶ − 1)

-- "999999 is divisible by 7" is the reason for the repeating block
example : 7 ∣ 10 ^ 6 - 1 := by decide
-- BOOK: end num-decimal

end Handbook.C06
