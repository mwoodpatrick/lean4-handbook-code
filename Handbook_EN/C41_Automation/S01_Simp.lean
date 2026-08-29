/- Chapter 41: Proof automation
   41.1 simp -- the simplifier -/
import Mathlib

namespace Handbook.C41

-- BOOK: begin simp-basic
-- simp keeps rewriting the registered equations from left to right
example (a : ℕ) : a + 0 = a := by simp
example (l : List ℕ) : (l ++ []).length = l.length := by simp
-- simp? displays the lemmas used, showing what did the work
example (a : ℕ) : a * 1 + 0 = a := by simp
-- BOOK: end simp-basic

-- BOOK: begin simp-only
-- simp only uses just the lemmas given, preventing a runaway
example (a b : ℕ) : a + b + 0 = a + b := by
  simp only [Nat.add_zero]
-- adding a lemma to simp
example (a : ℕ) (h : a = 5) : a + 0 = 5 := by simp [h]
-- BOOK: end simp-only

-- BOOK: begin simp-attr
-- @[simp] registers a lemma in the simp set
@[simp] theorem double_eq (n : ℕ) : 2 * n = n + n := by ring
example (n : ℕ) : 2 * n = n + n := by simp
-- BOOK: end simp-attr

-- BOOK: begin simp-loop
-- With a bad orientation simp does not stop: the right side must be
-- "simpler" than the left. Registering the line below would cycle,
-- a + b → b + a → a + b, so it is not registered.
example (a b : ℕ) : a + b = b + a := by
  rw [Nat.add_comm]
-- BOOK: end simp-loop

end Handbook.C41
