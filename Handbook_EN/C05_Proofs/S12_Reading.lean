/- English edition source: Handbook/C05_Proofs/S12_Reading.lean. -/
import Mathlib

namespace Handbook.C05

-- BOOK: begin read-show
-- show restates the goal in a definitionally equal form.
-- It can display on screen that the true form of ¬P is P → False.
example (P : Prop) (h : P → False) : ¬P := by
  show P → False
  exact h
-- BOOK: end read-show

-- BOOK: begin read-apply
-- apply goes to match the conclusion. When it does not match,
-- looking at "which argument was left over" reveals the cause.
example (a b c : ℕ) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  apply le_trans h1   -- the remaining goal is b ≤ c
  exact h2
-- BOOK: end read-apply

-- BOOK: begin read-cast
-- exact goes through only when the types match exactly.
-- If ℕ and ℤ are mixed, line up the types with push_cast.
example (n : ℕ) (h : 2 ≤ n) : (2 : ℤ) ≤ (n : ℤ) := by
  exact_mod_cast h
-- BOOK: end read-cast

-- BOOK: begin read-rw-fail
-- rw only rewrites "parts that match syntactically".
-- It does not reach under a binder, so use simp only.
example (f : ℕ → ℕ) (h : ∀ x, f x = x) :
    (fun y => f y) = fun y => y := by
  simp only [h]
-- BOOK: end read-rw-fail

-- BOOK: begin read-eps
-- A preview of analysis. If something is ≤ every positive number, it is
-- ≤ 0.
-- Three steps: contradiction → tidy up the negation → build a
-- counterexample ε yourself.
example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  by_contra hx
  push Not at hx        -- hx : 0 < x
  have h2 := h (x / 2) (by linarith)
  linarith
-- BOOK: end read-eps

end Handbook.C05
