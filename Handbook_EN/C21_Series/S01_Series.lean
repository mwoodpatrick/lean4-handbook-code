/- English edition source: Handbook/C21_Series/S01_Series.lean. -/
import Mathlib

namespace Handbook.C21

-- BOOK: begin tsum-geometric
-- The geometric series Σ (1/2)ⁿ = 2. ∑' is mathlib's sum (tsum).
example : ∑' n : ℕ, (1 / 2 : ℝ) ^ n = 2 := by
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

-- Summable f says that the series Σ f converges
example : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
  summable_geometric_of_lt_one (by norm_num) (by norm_num)
-- BOOK: end tsum-geometric

-- BOOK: begin harmonic
-- The harmonic series Σ 1/n diverges
example : ¬ Summable (fun n : ℕ => (1 : ℝ) / n) :=
  Real.not_summable_one_div_natCast
-- BOOK: end harmonic

-- BOOK: begin partial-sum
-- Convergence of a series means convergence of its partial sums
-- s_N = Σ_{n<N} f n (limits from Chapter 17).
-- A geometric partial sum has a closed form (for r ≠ 1).
example (r : ℝ) (hr : r ≠ 1) (N : ℕ) :
    ∑ n ∈ Finset.range N, r ^ n = (r ^ N - 1) / (r - 1) :=
  geom_sum_eq hr N
-- BOOK: end partial-sum

-- BOOK: begin div-test
-- The divergence test (a necessary condition): if the series
-- converges then the terms tend to 0.
-- Used contrapositively: if the terms do not tend to 0, it diverges.
example (f : ℕ → ℝ) (h : Summable f) :
    Filter.Tendsto f Filter.atTop (nhds 0) :=
  h.tendsto_atTop_zero
-- BOOK: end div-test

end Handbook.C21
