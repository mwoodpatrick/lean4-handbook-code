/- 第21章 無限級数
   21.4 交代級数 / 21.5 べき級数 / 21.6 e と π -/
import Mathlib

open Filter Topology

namespace Handbook.C21

-- BOOK: begin alternating
-- 交代級数の判定法。項が単調減少で 0 へ行けば収束する
example (f : ℕ → ℝ) (hf : Antitone f)
    (h0 : Tendsto f atTop (𝓝 0)) :
    ∃ l, Tendsto
      (fun n => ∑ i ∈ Finset.range n, (-1) ^ i * f i)
      atTop (𝓝 l) :=
  hf.tendsto_alternating_series_of_tendsto_zero h0
-- BOOK: end alternating

-- BOOK: begin tsum-ops
-- 総和は和と交換する。両方が Summable であることが要る
#check @Summable.tsum_add

-- 定数倍は外に出せる
#check @tsum_mul_left
-- BOOK: end tsum-ops

-- BOOK: begin power-radius
-- mathlib のべき級数は係数の列(多重線形写像の列)として持つ
#check @FormalMultilinearSeries.radius

-- 「f は a のまわり半径 r で級数展開できる」という述語
#check @HasFPowerSeriesOnBall
-- BOOK: end power-radius

-- BOOK: begin exp-series
-- 任意の x で ∑ xⁿ/n! は収束する(比判定法が効く形)
#check @Real.summable_pow_div_factorial

-- e = ∑ 1/n!。mathlib の exp はこの級数で定義されている
example : Real.exp 1 = ∑' n : ℕ, 1 / (n.factorial : ℝ) := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  simp
-- BOOK: end exp-series

-- BOOK: begin basel
-- バーゼル問題。Euler が 1735 年に示した値が入っている
example : ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 = Real.pi ^ 2 / 6 :=
  hasSum_zeta_two.tsum_eq
-- BOOK: end basel

end Handbook.C21
