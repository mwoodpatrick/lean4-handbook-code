/- English edition source: Handbook/AppA_Tactics/A04_More.lean. -/
import Mathlib

namespace Handbook.AppA

-- BOOK: begin t-by-contra
-- by_contra: assume the negation of the conclusion and derive a
-- contradiction
example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  by_contra hx
  push Not at hx
  have := h (x / 2) (by linarith)
  linarith
-- BOOK: end t-by-contra

-- BOOK: begin t-contrapose
-- contrapose!: take the contrapositive; with ! it also tidies up
-- negations
example (n : ℕ) (h : n ^ 2 ≠ 0) : n ≠ 0 := by
  contrapose! h
  rw [h]
  ring
-- BOOK: end t-contrapose

-- BOOK: begin t-cases
-- cases: split by each constructor; no induction hypothesis is attached
example (n : ℕ) : n = 0 ∨ 0 < n := by
  cases n with
  | zero => exact Or.inl rfl
  | succ k => exact Or.inr (Nat.succ_pos k)
-- BOOK: end t-cases

-- BOOK: begin t-leftright
-- left / right: choose which disjunct to prove
example : 2 = 2 ∨ 2 = 3 := by
  left
  rfl
-- BOOK: end t-leftright

-- BOOK: begin t-exfalso
-- exfalso: replace the goal with False (go and build a contradiction)
example (h : (1 : ℕ) = 2) : 3 = 4 := by
  exfalso
  omega
-- BOOK: end t-exfalso

-- BOOK: begin t-suffices
-- suffices: declare in advance that "it suffices to show this"
example (a b : ℝ) (h : a = b) : a + 0 = b := by
  suffices hs : a = b by simpa using hs
  exact h
-- BOOK: end t-suffices

-- BOOK: begin t-subst
-- subst: substitute throughout using an equation on a variable,
-- removing the hypothesis
example (a b : ℕ) (h : a = b) : a + 1 = b + 1 := by
  subst h
  rfl
-- BOOK: end t-subst

-- BOOK: begin t-nth-rewrite
-- nth_rewrite: specify which occurrence to rewrite
example (a : ℕ) (h : a = 0) : a + a = a := by
  nth_rewrite 1 [h]
  rw [Nat.zero_add]
-- BOOK: end t-nth-rewrite

-- BOOK: begin t-simp-rw
-- simp_rw: rewrite even inside binders.
-- The following does not go through with rw [h] (it does not reach
-- inside the λ)
example (f : ℕ → ℕ) (h : ∀ n, f n = n) :
    (fun n => f n) = (fun n => n) := by
  simp_rw [h]
-- BOOK: end t-simp-rw

-- BOOK: begin t-conv
-- conv: specify inside the goal where to rewrite.
-- conv_lhs targets only the left-hand side
example (a b : ℕ) (h : a = b) : a + a = b + b := by
  conv_lhs => rw [h]
-- BOOK: end t-conv

-- BOOK: begin t-splitifs
-- split_ifs: split the goal by each condition of an if
example (n : ℕ) : (if n = 0 then 0 else n) ≤ n := by
  split_ifs with h
  · exact Nat.zero_le n
  · exact le_refl n
-- BOOK: end t-splitifs

-- BOOK: begin t-interval-cases
-- interval_cases: enumerate all cases of a bounded variable
example (n : ℕ) (h1 : 2 ≤ n) (h2 : n < 5) :
    n = 2 ∨ n = 3 ∨ n = 4 := by
  interval_cases n
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
-- BOOK: end t-interval-cases

-- BOOK: begin t-tauto
-- tauto: close tautologies of propositional logic
example (p q : Prop) (h : p ∧ q) : q ∧ p := by tauto
-- BOOK: end t-tauto

-- BOOK: begin t-assumption
-- assumption / trivial: search the context / close a trivial goal
example (p : Prop) (hp : p) : p := by assumption

example : True ∧ (2 = 2) := by
  constructor
  · trivial
  · rfl
-- BOOK: end t-assumption

end Handbook.AppA
