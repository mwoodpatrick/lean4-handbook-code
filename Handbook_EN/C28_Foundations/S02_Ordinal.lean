/- English edition source: Handbook/C28_Foundations/S02_Ordinal.lean. -/
import Mathlib

namespace Handbook.C28

-- BOOK: begin ordinal-omega
-- The least infinite ordinal ω: the order type of the natural numbers
#check @Ordinal.omega0

-- Ordinal addition is not commutative: 1 + ω collapses back to ω
example : (1 : Ordinal) + Ordinal.omega0 = Ordinal.omega0 :=
  Ordinal.one_add_omega0

-- but ω + 1 is strictly larger than ω
example : Ordinal.omega0 < Ordinal.omega0 + 1 := by
  rw [← Order.succ_eq_add_one]
  exact Order.lt_succ _
-- BOOK: end ordinal-omega

-- BOOK: begin ordinal-noncomm
-- 1 + ω + 1: adding in front is absorbed, adding behind extends
example : (1 : Ordinal) + Ordinal.omega0 ≠ Ordinal.omega0 + 1 := by
  rw [Ordinal.one_add_omega0]
  refine ne_of_lt ?_
  rw [← Order.succ_eq_add_one]
  exact Order.lt_succ _
-- BOOK: end ordinal-noncomm

-- BOOK: begin ordinal-wf
-- The order < on the ordinals is well founded: no infinite
-- descending sequence exists
-- This provides the foundation for transfinite induction and
-- transfinite recursion.
#check @Ordinal.lt_wf

-- The well-ordering theorem: every type can be well ordered
-- (equivalent to the axiom of choice)
#check @exists_wellFoundedLT
-- BOOK: end ordinal-wf

end Handbook.C28
