/- English edition source: Handbook/AppA_Tactics/A03_Struct.lean. -/
import Mathlib

namespace Handbook.AppA

-- BOOK: begin t-induction
-- induction: mathematical induction; with names each case
example (n : ℕ) : 0 ≤ n := by
  induction n with
  | zero => exact le_refl 0
  | succ k ih => exact Nat.le_succ_of_le ih
-- BOOK: end t-induction

-- BOOK: begin t-by-cases
-- by_cases: split on the truth of a proposition (uses the law of
-- excluded middle)
example (p : Prop) [Decidable p] (q : Prop) (hq : q) :
    (p → q) ∧ (¬p → q) := by
  constructor
  · intro _; exact hq
  · intro _; exact hq

example (x : ℝ) : x ≤ |x| := by
  by_cases h : 0 ≤ x
  · rw [abs_of_nonneg h]
  · push Not at h
    rw [abs_of_neg h]
    linarith
-- BOOK: end t-by-cases

-- BOOK: begin t-ext
-- ext: reduce an equality to "equal at each point"
example (f g : ℕ → ℕ) (h : ∀ n, f n = g n) : f = g := by
  ext n
  exact h n

example (s t : Set ℕ) (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := by
  ext x
  exact h x
-- BOOK: end t-ext

-- BOOK: begin t-funext
-- funext: the dedicated version for equality of functions
example (f : ℕ → ℕ) : (fun n => f n) = f := by
  funext n
  rfl
-- BOOK: end t-funext

-- BOOK: begin t-push-neg
-- push Not: push negations inward. Turns ¬∀ into ∃¬.
-- The old name push_neg is deprecated in v4.32 (still works but warns)
example (f : ℕ → ℕ) (h : ¬ ∀ n, f n = 0) : ∃ n, f n ≠ 0 := by
  push Not at h
  exact h
-- BOOK: end t-push-neg

-- BOOK: begin t-specialize
-- specialize: specialize a universally quantified hypothesis to a
-- concrete value
example (f : ℕ → ℕ) (h : ∀ n, f n = n) : f 3 = 3 := by
  specialize h 3
  exact h
-- BOOK: end t-specialize

-- BOOK: begin t-have
-- have / show: state an auxiliary proposition / rewrite the goal in
-- another form
example (a b : ℝ) (h : a = b) : a + 1 = b + 1 := by
  have h2 : a + 1 = b + 1 := by rw [h]
  show a + 1 = b + 1
  exact h2
-- BOOK: end t-have

-- BOOK: begin t-set
-- set: name an expression and replace its occurrences in the goal all
-- at once
example (x y : ℝ) (h : x + y = 3) : (x + y) ^ 2 = 9 := by
  set s := x + y with hs
  rw [h]
  norm_num
-- BOOK: end t-set

-- BOOK: begin t-group
-- group / abel: close equalities in groups / commutative groups from
-- the axioms
example (G : Type) [Group G] (a b : G) :
    a * b * b⁻¹ = a := by group

example (A : Type) [AddCommGroup A] (a b : A) :
    a + b - b = a := by abel
-- BOOK: end t-group

-- BOOK: begin t-funprop
-- fun_prop: assemble continuity, measurability, and differentiability
-- from the syntax
example : Continuous (fun x : ℝ => x ^ 2 + Real.sin x) := by
  fun_prop

example : Differentiable ℝ (fun x : ℝ => Real.exp x * x) := by
  fun_prop
-- BOOK: end t-funprop

-- BOOK: begin t-aesop
-- aesop: rule-based proof search; strong on the chores of logic and
-- sets
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by aesop

example (s t : Set ℕ) (x : ℕ) (h : x ∈ s) : x ∈ s ∪ t := by
  aesop
-- BOOK: end t-aesop

-- BOOK: begin t-search
-- exact? searches the library for a lemma that closes the goal.
-- Replace it with the lemma name it finds (below is the form of that
-- search result)
example (a b : ℕ) (h : a ≤ b) : a ≤ b + 1 :=
  le_add_right h
-- BOOK: end t-search

end Handbook.AppA
