/- English edition source: Handbook/C05_Proofs/S10_Classical.lean. -/
import Mathlib

namespace Handbook.C05

-- BOOK: begin classical-em
-- Law of excluded middle: every proposition is either true or false
example (P : Prop) : P ∨ ¬P := Classical.em P

-- Splitting cases with excluded middle lets us cancel a double negation
example (P : Prop) (h : ¬¬P) : P := by
  rcases Classical.em P with hp | hnp
  · exact hp
  · exact absurd hnp h
-- BOOK: end classical-em

-- BOOK: begin classical-bycontra
-- Proof by contradiction: negate the conclusion and derive a
-- contradiction
example (n : ℕ) (h : n ^ 2 ≠ 0) : n ≠ 0 := by
  -- hn : n = 0 (the double negation is stripped automatically)
  by_contra hn
  apply h
  rw [hn]
  norm_num
-- BOOK: end classical-bycontra

-- BOOK: begin classical-pushneg
-- push Not pushes negations inside the quantifiers into a readable form
example : ¬ ∃ m : ℕ, ∀ n : ℕ, n ≤ m := by
  push Not   -- goal: ∀ m, ∃ n, m < n
  intro m
  exact ⟨m + 1, Nat.lt_succ_self m⟩
-- BOOK: end classical-pushneg

-- BOOK: begin classical-dne
-- Double-negation elimination. Not provable in constructive logic.
example (P : Prop) (h : ¬¬P) : P := Classical.byContradiction h

-- Peirce's law. It contains only implication yet requires classical
-- logic.
example (P Q : Prop) : ((P → Q) → P) → P := by
  intro h
  by_contra hnp
  exact hnp (h (fun hp => absurd hp hnp))
-- BOOK: end classical-dne

-- BOOK: begin classical-demorgan-quant
-- The quantifier version of De Morgan. Only the → direction needs
-- excluded middle.
example {α : Type} (P : α → Prop) :
    ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := by
  constructor
  · intro h
    by_contra hne
    push Not at hne      -- hne : ∀ x, P x
    exact h hne
  · rintro ⟨x, hx⟩ hall
    exact hx (hall x)
-- BOOK: end classical-demorgan-quant

-- BOOK: begin classical-axioms
-- You can audit which axioms a proof depends on with #print axioms
theorem em_used (P : Prop) : P ∨ ¬P := Classical.em P

#print axioms em_used
-- output: 'Handbook.C05.em_used' depends on axioms:
--         [Classical.choice, ...]
-- BOOK: end classical-axioms

end Handbook.C05
