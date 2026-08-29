/- English edition source: Handbook/C05_Proofs/S13_Decidable.lean. -/
import Mathlib

namespace Handbook.C05

-- BOOK: begin dec-decide
-- Decidable propositions can be verified by computation
example : 3 + 4 = 7 := by decide

example : ¬ (2 = 3) := by decide

-- Check whether a decision procedure is registered with inferInstance
#check (inferInstance : Decidable (3 < 5))
-- BOOK: end dec-decide

-- BOOK: begin dec-bounded
-- Bounded universals and existentials become decidable too
example : ∀ n < 5, n * n < 25 := by decide

example : ∃ n < 10, n * n = 49 := by decide
-- BOOK: end dec-bounded

-- BOOK: begin dec-limit
-- Remove the bound and it is undecidable. You have no choice but to
-- write a proof.
example : ∀ n : ℕ, 0 ≤ n := by
  intro n
  exact Nat.zero_le n
-- BOOK: end dec-limit

-- BOOK: begin dec-if
-- Decidable instances are also used for the branching of if
def sign (n : ℤ) : ℤ := if n < 0 then -1 else 1

example : sign (-3) = -1 := by decide

-- There is also the decide function, which reduces a proposition to
-- Bool
#eval decide (3 < 5)
-- BOOK: end dec-if

end Handbook.C05
