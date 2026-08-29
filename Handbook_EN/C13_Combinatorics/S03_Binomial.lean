/- English edition source: Handbook/C13_Combinatorics/S03_Binomial.lean. -/
import Mathlib

namespace Handbook.C13

-- BOOK: begin binomial
-- The binomial theorem. Nat.choose appears in the coefficients.
example (x y : ℚ) (n : ℕ) :
    (x + y) ^ n =
      ∑ k ∈ Finset.range (n + 1),
        x ^ k * y ^ (n - k) * (Nat.choose n k : ℚ) :=
  add_pow x y n
-- BOOK: end binomial

-- BOOK: begin binomial-sum
-- Setting x = y = 1 yields “the total number of subsets = 2ⁿ”
example (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Nat.choose n k = 2 ^ n :=
  Nat.sum_range_choose n
-- BOOK: end binomial-sum

end Handbook.C13
