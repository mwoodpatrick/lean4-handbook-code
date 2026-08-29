/- English edition source: Handbook/C05_Proofs/S06_Rewriting.lean. -/
import Mathlib

namespace Handbook.C05

-- BOOK: begin rw-basic
-- rw replaces the left side of an equation by the right side
example (a b : ℕ) (h : a = b) : a + 3 = b + 3 := by
  rw [h]

example (a b c : ℕ) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1, h2]
-- BOOK: end rw-basic

-- BOOK: begin rw-calc
-- calc lays out a chain of manipulations like a paper computation
example (a b : ℕ) (h1 : a = 2 * b) (h2 : b = 3) : a = 6 := by
  calc a = 2 * b := h1
    _ = 2 * 3 := by rw [h2]
    _ = 6 := rfl
-- BOOK: end rw-calc

-- BOOK: begin rw-at
-- rw rewrites not only the goal but also the hypotheses
example (a b : ℕ) (h1 : a = b) (h2 : a + 1 = 5) :
    b + 1 = 5 := by
  rw [h1] at h2
  exact h2

-- to rewrite backwards, use ←
example (a b : ℕ) (h : a = b) : b + 3 = a + 3 := by
  rw [← h]
-- BOOK: end rw-at

-- BOOK: begin rw-calc-ineq
-- calc works for chains of inequalities too, not only equalities
example (a b : ℕ) (h : a ≤ b) : a ≤ b + 3 := by
  calc a ≤ b := h
    _ ≤ b + 3 := Nat.le_add_right b 3
-- BOOK: end rw-calc-ineq

end Handbook.C05
