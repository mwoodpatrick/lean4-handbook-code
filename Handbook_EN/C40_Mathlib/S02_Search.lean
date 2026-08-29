/- English edition source: Handbook/C40_Mathlib/S02_Search.lean. -/
import Mathlib

namespace Handbook.C40

-- BOOK: begin search-exact
-- exact? searches for a lemma closing the current goal
example (a b : ℕ) (h : a ≤ b) : a ≤ b + 1 := by
  exact?
-- BOOK: end search-exact

-- BOOK: begin search-apply
-- Writing down the lemma exact? found makes it go through without
-- searching again.
example (a b : ℕ) (h : a ≤ b) : a ≤ b + 1 :=
  Nat.le_succ_of_le h

-- If it is already a hypothesis use assumption;
-- if simp lemmas close it, use simp
example (a b : ℕ) (h : a ≤ b) : a ≤ b := by assumption
example (a : ℕ) : a ∈ {x : ℕ | x = a} := by simp
-- BOOK: end search-apply

-- BOOK: begin search-check
-- #check confirms a name and displays its type
#check @Nat.le_succ_of_le
#check @Nat.succ_le_of_lt
#check @Nat.lt_succ_iff
-- BOOK: end search-check

end Handbook.C40
