/- English edition source: Handbook/C05_Proofs/S11_Patterns.lean. -/
import Mathlib

namespace Handbook.C05

-- BOOK: begin pat-anon
-- ⟨ ⟩ is used both to "build a tuple" and to "take a tuple apart"
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := ⟨hp, hq⟩

-- Since it is right-associative, ⟨hp, hq, hr⟩ abbreviates ⟨hp, ⟨hq,
-- hr⟩⟩
example (P Q R : Prop) (h : P ∧ Q ∧ R) : R ∧ P := by
  obtain ⟨hp, _, hr⟩ := h
  exact ⟨hr, hp⟩
-- BOOK: end pat-anon

-- BOOK: begin pat-or
-- | branches on a disjunction; separate with a vertical bar for each
-- branch
example (P Q R : Prop) (h : P ∨ Q ∨ R) : R ∨ Q ∨ P := by
  rcases h with hp | hq | hr
  · exact Or.inr (Or.inr hp)
  · exact Or.inr (Or.inl hq)
  · exact Or.inl hr
-- BOOK: end pat-or

-- BOOK: begin pat-mixed
-- Products and sums can be nested; the shape just has to match that of
-- the hypothesis
example (P Q R : Prop) (h : (P ∧ Q) ∨ R) : P ∨ R := by
  rcases h with ⟨hp, _⟩ | hr
  · exact Or.inl hp
  · exact Or.inr hr
-- BOOK: end pat-mixed

-- BOOK: begin pat-rfl
-- The rfl pattern consumes an equality hypothesis on the spot and
-- eliminates the variable
example (a b : ℕ) (h : ∃ k, a = b + k) : b ≤ a := by
  obtain ⟨k, rfl⟩ := h
  exact Nat.le_add_right b k
-- BOOK: end pat-rfl

-- BOOK: begin pat-rintro
-- rintro composes intro and rcases: it takes and decomposes at the same
-- time
example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  rintro ⟨hp, hq⟩
  exact ⟨hq, hp⟩

-- Discard the parts you do not use with _ (naming them raises an
-- unused-variable warning)
example (P Q : Prop) : P ∧ Q → P := by
  rintro ⟨hp, _⟩
  exact hp
-- BOOK: end pat-rintro

end Handbook.C05
