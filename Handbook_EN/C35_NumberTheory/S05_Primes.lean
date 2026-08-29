/- Chapter 35: Number theory
   35.6 The distribution of the primes -/
import Mathlib

namespace Handbook.C35

-- BOOK: begin infinitude
-- There are infinitely many primes (Euclid, about 300 BC)
example (n : ℕ) : ∃ p, n ≤ p ∧ p.Prime :=
  Nat.exists_infinite_primes n
-- BOOK: end infinitude

-- BOOK: begin bertrand
-- Bertrand's postulate: there is always a prime between n and 2n
example (n : ℕ) (hn : n ≠ 0) : ∃ p, p.Prime ∧ n < p ∧ p ≤ 2 * n :=
  Nat.bertrand n hn

-- checking it at n = 10: 11, 13, 17, 19 fall in the range
example : Nat.Prime 11 ∧ 10 < 11 ∧ 11 ≤ 20 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩
-- BOOK: end bertrand

-- BOOK: begin prime-counting
-- The prime counting function: π(10) = 4 (namely 2, 3, 5, 7)
example : (Finset.range 11).filter Nat.Prime = {2, 3, 5, 7} := by
  decide

-- uniqueness of prime factorization
-- (the fundamental theorem of arithmetic, Chapter 14)
example (n : ℕ) (hn : n ≠ 0) :
    n = n.factorization.prod (· ^ ·) :=
  (Nat.prod_factorization_pow_eq_self hn).symm
-- BOOK: end prime-counting

end Handbook.C35
