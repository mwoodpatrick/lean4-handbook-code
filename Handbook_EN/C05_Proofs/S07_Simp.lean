/- English edition source: Handbook/C05_Proofs/S07_Simp.lean. -/
import Mathlib

namespace Handbook.C05

-- BOOK: begin simp-basic
-- simp applies "simplification-oriented equalities" repeatedly
example (a : ℕ) : (a + 0) * 1 = a := by simp

example (xs : List ℕ) : (xs ++ []).length = xs.length := by
  simp
-- BOOK: end simp-basic

-- BOOK: begin simp-only
-- simp only names the lemmas to use (a simp that will not run wild)
example (a b : ℕ) : a + 0 + (b + 0) = a + b := by
  simp only [Nat.add_zero]
-- BOOK: end simp-only

-- BOOK: begin simp-at
-- To simplify a hypothesis, add at
example (a b : ℕ) (h : a + 0 = b) : a = b := by
  simp at h
  exact h
-- BOOK: end simp-at

-- BOOK: begin simp-with
-- Pass a hypothesis as a simplification rule (simp only [h])
example (a b : ℕ) (h : b = 2 * a) : a + b = 3 * a := by
  simp only [h]
  ring
-- BOOK: end simp-with

end Handbook.C05
