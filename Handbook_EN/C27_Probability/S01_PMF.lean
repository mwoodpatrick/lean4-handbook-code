/- English edition source: Handbook/C27_Probability/S01_PMF.lean. -/
import Mathlib

namespace Handbook.C27

open MeasureTheory

-- BOOK: begin prob-measure
-- A probability measure: the measure of the whole space is 1
example (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    μ Set.univ = 1 :=
  measure_univ
-- BOOK: end prob-measure

-- BOOK: begin pmf
-- A discrete distribution is a PMF (probability mass function).
-- A fair coin. ofFintype takes the probability of each value
-- together with a proof that they sum to 1.
noncomputable def coin : PMF Bool :=
  PMF.ofFintype (fun _ => 1 / 2) (by
    rw [Finset.sum_const]
    simp only [Finset.card_univ, Fintype.card_bool, nsmul_eq_mul,
      Nat.cast_ofNat]
    rw [one_div, ENNReal.mul_inv_cancel] <;> norm_num)

-- the probabilities sum to 1 (the axiom of a PMF itself)
example : ∑' b, coin b = 1 := coin.tsum_coe
-- BOOK: end pmf

-- BOOK: begin pmf-value
-- The probability of heads (true) for a fair coin is 1/2
example : coin true = 1 / 2 := by
  simp [coin, PMF.ofFintype_apply]
-- BOOK: end pmf-value

-- BOOK: begin pmf-bind
-- bind: draw a value from one distribution and then choose the next
-- one (two experiments in a row).
-- The value of bind sums the probabilities over the routes.
example (p : PMF Bool) (f : Bool → PMF Bool) (b : Bool) :
    (p.bind f) b = ∑' a, p a * f a b :=
  PMF.bind_apply p f b
-- BOOK: end pmf-bind

end Handbook.C27
