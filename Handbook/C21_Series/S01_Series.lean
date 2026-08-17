/- 第21章 無限級数
   21.1 部分和と級数の収束 / 21.2 tsum -/
import Mathlib

namespace Handbook.C21

-- BOOK: begin tsum-geometric
-- 幾何級数 Σ (1/2)ⁿ = 2。∑' が mathlib の総和(tsum)。
example : ∑' n : ℕ, (1 / 2 : ℝ) ^ n = 2 := by
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

-- Summable f は「級数 Σ f が収束する」
example : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
  summable_geometric_of_lt_one (by norm_num) (by norm_num)
-- BOOK: end tsum-geometric

-- BOOK: begin harmonic
-- 調和級数 Σ 1/n は発散する
example : ¬ Summable (fun n : ℕ => (1 : ℝ) / n) :=
  Real.not_summable_one_div_natCast
-- BOOK: end harmonic

-- BOOK: begin partial-sum
-- 級数の収束 = 部分和 s_N = Σ_{n<N} f n の収束(第17章の極限)
-- 幾何級数の部分和は閉じた式を持つ(r ≠ 1)
example (r : ℝ) (hr : r ≠ 1) (N : ℕ) :
    ∑ n ∈ Finset.range N, r ^ n = (r ^ N - 1) / (r - 1) :=
  geom_sum_eq hr N
-- BOOK: end partial-sum

-- BOOK: begin div-test
-- 発散判定法(必要条件): 収束するなら一般項は 0 に近づく
-- 対偶: 一般項が 0 に行かなければ発散する
example (f : ℕ → ℝ) (h : Summable f) :
    Filter.Tendsto f Filter.atTop (nhds 0) :=
  h.tendsto_atTop_zero
-- BOOK: end div-test

end Handbook.C21
