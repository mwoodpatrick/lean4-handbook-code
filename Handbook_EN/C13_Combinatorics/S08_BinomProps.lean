/- Chapter 13: Counting and probability
   13.3 Properties of the binomial coefficients -/
import Mathlib

namespace Handbook.C13

-- antidiagonal k is Finset.antidiagonal: the pairs (i, j) with i + j = k
open Finset

-- BOOK: begin bin-pascal
-- Pascal's rule: each entry is the sum of the two above it
example (n k : ℕ) :
    (n + 1).choose (k + 1) = n.choose k + n.choose (k + 1) :=
  Nat.choose_succ_succ n k
-- BOOK: end bin-pascal

-- BOOK: begin bin-symm
-- Symmetry: choosing k and leaving n - k are the same act
example (n k : ℕ) (h : k ≤ n) :
    n.choose (n - k) = n.choose k :=
  Nat.choose_symm h
-- BOOK: end bin-symm

-- BOOK: begin bin-rowsum
-- The row sum is 2^n: count the subsets in two ways
example (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), n.choose i = 2 ^ n :=
  Nat.sum_range_choose n
-- BOOK: end bin-rowsum

-- BOOK: begin bin-vandermonde
-- Vandermonde's convolution: split k items between two boxes
example (m n k : ℕ) :
    (m + n).choose k
      = ∑ ij ∈ antidiagonal k, m.choose ij.1 * n.choose ij.2 :=
  Nat.add_choose_eq m n k
-- BOOK: end bin-vandermonde

end Handbook.C13
