/- 第27章 確率論の基礎
   27.1 確率空間の公理 / 27.7 PMF -/
import Mathlib

namespace Handbook.C27

open MeasureTheory

-- BOOK: begin prob-measure
-- 確率測度: 全体の測度が 1 の測度
example (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    μ Set.univ = 1 :=
  measure_univ
-- BOOK: end prob-measure

-- BOOK: begin pmf
-- 離散確率分布は PMF(確率質量関数)。公平なコイン。
-- ofFintype: 各値の確率を与え、総和が 1 であることを示して作る
noncomputable def coin : PMF Bool :=
  PMF.ofFintype (fun _ => 1 / 2) (by
    rw [Finset.sum_const]
    simp only [Finset.card_univ, Fintype.card_bool, nsmul_eq_mul,
      Nat.cast_ofNat]
    rw [one_div, ENNReal.mul_inv_cancel] <;> norm_num)

-- 全確率は 1(PMF の公理そのもの)
example : ∑' b, coin b = 1 := coin.tsum_coe
-- BOOK: end pmf

-- BOOK: begin pmf-value
-- 公平なコインで表(true)が出る確率は 1/2
example : coin true = 1 / 2 := by
  simp [coin, PMF.ofFintype_apply]
-- BOOK: end pmf-value

-- BOOK: begin pmf-bind
-- bind: 分布から値を取り、その値で次の分布を選ぶ(二段階の実験)
-- bind の値は「経路の確率の総和」Σ p a * f a b
example (p : PMF Bool) (f : Bool → PMF Bool) (b : Bool) :
    (p.bind f) b = ∑' a, p a * f a b :=
  PMF.bind_apply p f b
-- BOOK: end pmf-bind

end Handbook.C27
