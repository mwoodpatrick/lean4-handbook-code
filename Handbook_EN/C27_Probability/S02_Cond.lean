/- English edition source: Handbook/C27_Probability/S02_Cond.lean. -/
import Mathlib

namespace Handbook.C27

open MeasureTheory ProbabilityTheory

-- BOOK: begin cond-def
-- The conditional probability μ[t | s] is the measure obtained by
-- restricting to s and renormalizing.
-- P(s ∩ t) / P(s)
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    {s : Set Ω} (hs : MeasurableSet s) (t : Set Ω) :
    μ[t | s] = (μ s)⁻¹ * μ (s ∩ t) :=
  ProbabilityTheory.cond_apply hs μ t
-- BOOK: end cond-def

-- BOOK: begin cond-chain
-- The multiplication rule: P(s ∩ t) = P(s) · P(t | s),
-- the definition of conditional probability with the denominator
-- cleared
#check @ProbabilityTheory.cond_mul_eq_inter

-- conditioning twice is the same as conditioning on the intersection
#check @ProbabilityTheory.cond_cond_eq_cond_inter
-- BOOK: end cond-chain

-- BOOK: begin indep-def
-- Independence, defined for two events and for two random variables
#check @ProbabilityTheory.IndepSet
#check @ProbabilityTheory.IndepFun

-- For three or more events, independence means that every finite
-- subfamily factors as a product.
-- It is stronger than pairwise independence.
#check @ProbabilityTheory.iIndepFun
-- BOOK: end indep-def

end Handbook.C27
