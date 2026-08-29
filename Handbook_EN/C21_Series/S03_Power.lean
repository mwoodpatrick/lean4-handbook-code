/- English edition source: Handbook/C21_Series/S03_Power.lean. -/
import Mathlib

open Filter Topology

namespace Handbook.C21

-- BOOK: begin alternating
-- The alternating series test: it converges if the terms decrease
-- monotonically to 0
example (f : ℕ → ℝ) (hf : Antitone f)
    (h0 : Tendsto f atTop (𝓝 0)) :
    ∃ l, Tendsto
      (fun n => ∑ i ∈ Finset.range n, (-1) ^ i * f i)
      atTop (𝓝 l) :=
  hf.tendsto_alternating_series_of_tendsto_zero h0
-- BOOK: end alternating

-- BOOK: begin tsum-ops
-- Sums may be added termwise, provided both are Summable
#check @Summable.tsum_add

-- a constant factor comes out of the sum
#check @tsum_mul_left
-- BOOK: end tsum-ops

-- BOOK: begin power-radius
-- mathlib holds a power series as a sequence of coefficients
-- (a formal multilinear series)
#check @FormalMultilinearSeries.radius

-- The predicate says that f admits a power-series expansion around a
-- with radius r.
#check @HasFPowerSeriesOnBall
-- BOOK: end power-radius

-- BOOK: begin exp-series
-- Σ xⁿ/n! converges for every x (shown by the ratio test)
#check @Real.summable_pow_div_factorial

-- e = ∑ 1/n!. mathlib defines exp by this series.
example : Real.exp 1 = ∑' n : ℕ, 1 / (n.factorial : ℝ) := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  simp
-- BOOK: end exp-series

-- BOOK: begin basel
-- The Basel problem. The value Euler found in 1735 is recorded.
example : ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 = Real.pi ^ 2 / 6 :=
  hasSum_zeta_two.tsum_eq
-- BOOK: end basel

end Handbook.C21
