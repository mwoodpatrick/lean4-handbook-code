/- English edition source: Handbook/C25_ODE/S03_Unique.lean. -/
import Mathlib

open Set

namespace Handbook.C25

-- BOOK: begin unique-exist
-- The hypotheses of Picard--Lindelöf are bundled into a structure
#check @IsPicardLindelof

-- Existence: under those hypotheses a solution can be constructed
#check @IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt
-- BOOK: end unique-exist

-- BOOK: begin unique-main
-- Uniqueness: if v is Lipschitz, two solutions with the same initial
-- value agree on the interval
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℝ → E → E) (K : NNReal) (f g : ℝ → E) (a b : ℝ)
    (hv : ∀ t, LipschitzWith K (v t))
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (v t (f t)) (Ici t) t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (v t (g t)) (Ici t) t)
    (ha : f a = g a) : EqOn f g (Icc a b) :=
  ODE_solution_unique hv hf hf' hg hg' ha
-- BOOK: end unique-main

-- BOOK: begin unique-gronwall
-- Gronwall inequality. When an error occurs proportionally to itself,
-- The growth can be bounded by an exponential function.
#check @gronwallBound
#check @norm_le_gronwallBound_of_norm_deriv_right_le
-- BOOK: end unique-gronwall

-- BOOK: begin unique-dist
-- The distance between two trajectories whose initial values ​​deviate
-- can also be suppressed by an exponential function.
-- This is the continuous dependence of the solution on the initial
-- value.
#check @dist_le_of_trajectories_ODE
-- BOOK: end unique-dist

end Handbook.C25
