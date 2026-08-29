/- Chapter 3: Setting up the environment
   3.4 Your first proof -/
import Mathlib

namespace Handbook.C03

-- BOOK: begin first-proof
-- If the environment works, these two lines get a green check
theorem my_first_proof : 2 + 2 = 4 := rfl
-- BOOK: end first-proof

-- BOOK: begin check-mathlib
-- Checking that mathlib has loaded.
-- If the primality test goes through, mathlib is running too,
-- not only the standard library
example : Nat.Prime 97 := by norm_num
-- are the reals and limits available? (the analysis part of mathlib)
#check @Real.sqrt
#check @Filter.Tendsto
-- BOOK: end check-mathlib

-- BOOK: begin first-tactic
-- The first proof written with tactics.
-- intro brings in the hypotheses and exact fits them to the goal
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp
  · exact hq
-- BOOK: end first-tactic

end Handbook.C03
