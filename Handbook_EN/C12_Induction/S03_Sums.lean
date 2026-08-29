/- English edition source: Handbook/C12_Induction/S03_Sums.lean. -/
import Mathlib

namespace Handbook.C12

-- BOOK: begin sum-eval
-- Σ is Finset.sum. We write it as a sum over range n = {0, 1, …, n-1}.
open Finset in
#eval ∑ i ∈ range 5, i ^ 2  -- output: 30
-- BOOK: end sum-eval

-- BOOK: begin gauss
-- Gauss's sum 1 + 2 + ⋯ + n = n(n+1)/2, stated after doubling to avoid
-- division.
theorem gauss_sum (n : ℕ) :
    2 * ∑ i ∈ Finset.range (n + 1), i = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    ring
-- BOOK: end gauss

-- BOOK: begin gauss-mathlib
-- mathlib already contains a lemma with the same content
example (n : ℕ) :
    (∑ i ∈ Finset.range n, i) * 2 = n * (n - 1) :=
  Finset.sum_range_id_mul_two n
-- BOOK: end gauss-mathlib

-- BOOK: begin geom-sum
-- Sum of a geometric progression. Over the field ℚ it can be written as
-- a quotient (r ≠ 1).
example (r : ℚ) (hr : r ≠ 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, r ^ i = (r ^ n - 1) / (r - 1) :=
  geom_sum_eq hr n
-- BOOK: end geom-sum

-- BOOK: begin telescope
-- Telescoping sum: summing adjacent differences leaves only the two
-- endpoints
example (f : ℕ → ℤ) (n : ℕ) :
    ∑ i ∈ Finset.range n, (f (i + 1) - f i) = f n - f 0 :=
  Finset.sum_range_sub f n
-- BOOK: end telescope

-- BOOK: begin sum-squares
-- Formula for the sum of squares, stated after multiplying by 6 to
-- avoid division.
theorem sum_sq (n : ℕ) :
    6 * ∑ i ∈ Finset.range (n + 1), i ^ 2
      = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    ring
-- BOOK: end sum-squares

end Handbook.C12
