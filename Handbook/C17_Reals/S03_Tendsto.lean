/- 第17章 実数と数列の極限
   17.4 Filter.Tendsto — mathlib の極限語法 -/
import Mathlib

namespace Handbook.C17

open Filter Topology

-- BOOK: begin tendsto-def
-- mathlib の極限: Tendsto a atTop (𝓝 L)
-- 「n を限りなく大きくすると a n は L の近傍に入る」
example : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat
-- BOOK: end tendsto-def

-- BOOK: begin tendsto-epsn
-- Tendsto と ε-N は同値である(距離空間では)
example (a : ℕ → ℝ) (L : ℝ) :
    Tendsto a atTop (𝓝 L) ↔
      ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| < ε := by
  rw [Metric.tendsto_atTop]
  simp [Real.dist_eq]
-- BOOK: end tendsto-epsn

end Handbook.C17
