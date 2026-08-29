/- Chapter 17: Real numbers and limits of sequences
   17.4 Filter.Tendsto -- mathlib's language of limits -/
import Mathlib

open Filter Topology

namespace Handbook.C17

-- BOOK: begin tendsto-basic
-- mathlib's limit: Tendsto a atTop (𝓝 L)
-- "make n grow without bound and a n enters every neighborhood of L"
example : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat
-- BOOK: end tendsto-basic

-- BOOK: begin tendsto-epsn
-- Tendsto and ε-N are equivalent (in a metric space)
example (a : ℕ → ℝ) (L : ℝ) :
    Tendsto a atTop (𝓝 L) ↔
      ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| < ε := by
  rw [Metric.tendsto_atTop]
  simp [Real.dist_eq]
-- BOOK: end tendsto-epsn

end Handbook.C17
