/- English edition source: Handbook/AppA_Tactics/A01_Basic.lean. -/
import Mathlib

namespace Handbook.AppA

-- BOOK: begin t-exact
-- exact: match a term to the goal exactly
example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  ⟨hp, hq⟩

example (p : Prop) (hp : p) : p := by exact hp
-- BOOK: end t-exact

-- BOOK: begin t-apply
-- apply: work the goal backwards into the hypotheses of a lemma
example (p q : Prop) (h : p → q) (hp : p) : q := by
  apply h
  exact hp
-- BOOK: end t-apply

-- BOOK: begin t-intro
-- intro: move the antecedent of an implication / a universally
-- quantified variable into the hypotheses
example (p q : Prop) : p → q → p := by
  intro hp _
  exact hp

example (f : ℕ → ℕ) (h : ∀ n, f n = n) : ∀ n, f n = n := by
  intro n
  exact h n
-- BOOK: end t-intro

-- BOOK: begin t-rfl
-- rfl: close things equal by definition; computation proceeds by
-- reduction
example : 2 + 2 = 4 := rfl

example (l : List ℕ) : l ++ [] = l := by simp
-- BOOK: end t-rfl

-- BOOK: begin t-rw
-- rw: rewrite by an equation; ← goes right to left
example (a b c : ℕ) (h : a = b) : a + c = b + c := by
  rw [h]

example (a b : ℕ) (h : a = b) : b = a := by
  rw [← h]
-- BOOK: end t-rw

-- BOOK: begin t-use
-- use: supply a witness for an existential
example : ∃ n : ℕ, n * n = 49 := by
  use 7
-- BOOK: end t-use

-- BOOK: begin t-obtain
-- obtain: decompose a structure and extract from it (open up ∃ or ∧)
example (p q : Prop) (h : p ∧ q) : q := by
  obtain ⟨_, hq⟩ := h
  exact hq

example (f : ℕ → ℕ) (h : ∃ n, f n = 0) : True := by
  obtain ⟨n, hn⟩ := h
  trivial
-- BOOK: end t-obtain

-- BOOK: begin t-rintro
-- rintro: perform intro and decomposition in one step
example (p q : Prop) : p ∧ q → q := by
  rintro ⟨_, hq⟩
  exact hq
-- BOOK: end t-rintro

-- BOOK: begin t-constructor
-- constructor: apply the constructor (split ∧ into two goals)
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp
  · exact hq
-- BOOK: end t-constructor

-- BOOK: begin t-refine
-- refine: give a partial witness and leave the rest as holes ?_
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  refine ⟨hp, ?_⟩
  exact hq
-- BOOK: end t-refine

-- BOOK: begin t-rcases
-- rcases: split into cases by pattern (split up ∨)
example (p q : Prop) (h : p ∨ q) : q ∨ p := by
  rcases h with hp | hq
  · exact Or.inr hp
  · exact Or.inl hq
-- BOOK: end t-rcases

-- BOOK: begin t-calc
-- calc: chain equalities and inequalities step by step
example (a b : ℕ) (h1 : a = b) (h2 : b ≤ 5) : a ≤ 5 :=
  calc a = b := h1
    _ ≤ 5 := h2
-- BOOK: end t-calc

end Handbook.AppA
