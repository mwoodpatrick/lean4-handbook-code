/- English edition source: Handbook/C40_Mathlib/S04_Design.lean. -/
import Mathlib

namespace Handbook.C40

-- BOOK: begin design-general
-- The gain from generality: add_comm works in every commutative
-- monoid
#check @add_comm

-- the same single theorem serves for ℕ and for ℝ
example (a b : ℕ) : a + b = b + a := add_comm a b
example (a b : ℝ) : a + b = b + a := add_comm a b
example (a b : Polynomial ℤ) : a + b = b + a := add_comm a b
-- BOOK: end design-general

-- BOOK: begin design-cost
-- The cost of generality: the concrete type disappears from the name
-- and it becomes harder to search for.
-- The ℕ-specific name survives, with the same content as the
-- general version.
#check @Nat.add_comm
#check @add_comm

-- Written in the general form, a proof still works when the type is
-- changed later
example (R : Type) [AddCommMonoid R] (a b c : R) :
    a + b + c = c + (b + a) := by
  rw [add_comm a b, add_comm (b + a) c]
-- BOOK: end design-cost

end Handbook.C40
