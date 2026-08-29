/- English edition source: Handbook/C14_Integers/S05_Fermat.lean. -/
import Mathlib

namespace Handbook.C14

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

-- BOOK: begin fermat-eval
-- First observe numerically: 2⁶ = 64 = 7 × 9 + 1
#eval (2 ^ 6 : ZMod 7)  -- output: 1
#eval (3 ^ 6 : ZMod 7)  -- output: 1
#eval (5 ^ 6 : ZMod 7)  -- output: 1
-- BOOK: end fermat-eval

-- BOOK: begin fermat-little
-- Fermat’s little theorem: if p is prime and a ≢ 0, then a^(p-1) ≡ 1
example (a : ZMod 7) (ha : a ≠ 0) : a ^ 6 = 1 :=
  ZMod.pow_card_sub_one_eq_one ha
-- BOOK: end fermat-little

-- BOOK: begin omega-demo
-- omega: a decision procedure for linear arithmetic over integers and
-- naturals
example (a b : ℤ) (h : 2 * a + 6 * b = 5) : False := by omega

example (n : ℕ) : (n + 7) % 7 = n % 7 := by omega
-- BOOK: end omega-demo

-- BOOK: begin totient
-- Euler’s totient φ(n): the number of values below n that are coprime
-- to n
#eval Nat.totient 12  -- output: 4 (1, 5, 7, 11)
#eval Nat.totient 7   -- output: 6 (p−1 for a prime p)

example : Nat.totient 12 = 4 := by decide
-- BOOK: end totient

-- BOOK: begin integers-exercises
-- Exercises: Euclidean algorithm, congruences, and divisibility
example : Nat.gcd 84 60 = 12 := by decide

example : (10 : ZMod 7) = 3 := by decide

example (a : ℤ) (h : 4 ∣ a) : 2 ∣ a := by omega
-- BOOK: end integers-exercises

end Handbook.C14
