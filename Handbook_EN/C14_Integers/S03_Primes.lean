/- English edition source: Handbook/C14_Integers/S03_Primes.lean. -/
import Mathlib

namespace Handbook.C14

-- BOOK: begin prime-basic
example : Nat.Prime 13 := by norm_num

-- Every natural number other than 1 has a prime factor
example (n : ℕ) (h : 2 ≤ n) : ∃ p, p.Prime ∧ p ∣ n :=
  Nat.exists_prime_and_dvd (by omega)
-- BOOK: end prime-basic

-- BOOK: begin prime-factors
-- Prime factorization can be computed as a list
#eval Nat.primeFactorsList 360  -- output: [2, 2, 2, 3, 3, 5]

-- Multiplying the factorization recovers the original number (when
-- nonzero)
example (n : ℕ) (hn : n ≠ 0) :
    (Nat.primeFactorsList n).prod = n :=
  Nat.prod_primeFactorsList hn
-- BOOK: end prime-factors

-- BOOK: begin prime-euclid-lemma
-- The essence of primality (Euclid’s lemma): if a prime divides a
-- product, it divides one factor
example (p a b : ℕ) (hp : p.Prime) (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b :=
  hp.dvd_mul.mp h

-- This fails for the composite 6: 6 ∣ 4·9 but 6 ∤ 4 and 6 ∤ 9
example : (6 ∣ 4 * 9) ∧ ¬(6 ∣ 4) ∧ ¬(6 ∣ 9) := by decide
-- BOOK: end prime-euclid-lemma

-- BOOK: begin divisors
-- The set, number, and sum of divisors are all computable
#eval (12 : ℕ).divisors         -- output: {1, 2, 3, 4, 6, 12}
#eval (12 : ℕ).divisors.card    -- output: 6
#eval (12 : ℕ).divisors.sum id  -- output: 28

-- 6 is perfect: the sum of its proper divisors (1+2+3) equals itself
example : (6 : ℕ).divisors.sum id = 2 * 6 := by decide
-- BOOK: end divisors

end Handbook.C14
