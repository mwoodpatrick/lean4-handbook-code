/- Chapter 12: Sequences and mathematical induction
   12.3 Rules for manipulating sums -/
import Mathlib

namespace Handbook.C12

-- BOOK: begin rule-linear
-- Sums split and constant factors come out: summation is linear
example (n : ℕ) (f g : ℕ → ℚ) :
    ∑ i ∈ Finset.range n, (f i + g i)
      = (∑ i ∈ Finset.range n, f i)
        + ∑ i ∈ Finset.range n, g i :=
  Finset.sum_add_distrib

example (n : ℕ) (c : ℚ) (f : ℕ → ℚ) :
    ∑ i ∈ Finset.range n, c * f i
      = c * ∑ i ∈ Finset.range n, f i := by
  rw [Finset.mul_sum]
-- BOOK: end rule-linear

-- BOOK: begin rule-const
-- A sum of constants is the constant times the count
example (n : ℕ) (c : ℚ) :
    ∑ _i ∈ Finset.range n, c = n * c := by
  simp [Finset.sum_const, nsmul_eq_mul]
-- BOOK: end rule-const

-- BOOK: begin rule-swap
-- A double sum may be exchanged unconditionally
example (m n : ℕ) (f : ℕ → ℕ → ℚ) :
    ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, f i j
      = ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range m, f i j :=
  Finset.sum_comm
-- BOOK: end rule-swap

-- BOOK: begin rule-prod
-- Products obey the paired rules: sum_ becomes prod_
example (n : ℕ) (f : ℕ → ℚ) :
    ∏ i ∈ Finset.range (n + 1), f i
      = (∏ i ∈ Finset.range n, f i) * f n :=
  Finset.prod_range_succ f n

example (n : ℕ) (c : ℚ) :
    ∏ _i ∈ Finset.range n, c = c ^ n := by
  simp
-- BOOK: end rule-prod

end Handbook.C12
