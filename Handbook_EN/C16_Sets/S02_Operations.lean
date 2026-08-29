/- English edition source: Handbook/C16_Sets/S02_Operations.lean. -/
import Mathlib

namespace Handbook.C16

open Set

-- BOOK: begin set-ops
example (A B : Set ℕ) : A ∩ B ⊆ A := inter_subset_left

example (A B : Set ℕ) : A ⊆ A ∪ B := subset_union_left

-- De Morgan’s law
example (A B : Set ℕ) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := compl_union A B
-- BOOK: end set-ops

-- BOOK: begin set-inter-union
-- An intersection is contained in the union: take x in A ∩ B, keep
-- the left half, and put it into the union
example (A B : Set ℕ) : A ∩ B ⊆ A ∪ B := by
  intro x hx
  exact Or.inl hx.1
-- BOOK: end set-inter-union

-- BOOK: begin set-antisymm
-- Equality of sets is inclusion in both directions (extensionality)
example (A B : Set ℕ) (h1 : A ⊆ B) (h2 : B ⊆ A) : A = B :=
  Subset.antisymm h1 h2

-- The standard form: take an element and prove membership
example (A B C : Set ℕ) (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C := by
  intro x hx
  exact h2 (h1 hx)
-- BOOK: end set-antisymm

-- BOOK: begin set-distrib
-- Distributivity: ext takes an element; the rest reduces to the logic
-- of Chapter 5
example (A B C : Set ℕ) :
    A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  constructor
  · rintro ⟨hA, hB | hC⟩
    · exact Or.inl ⟨hA, hB⟩
    · exact Or.inr ⟨hA, hC⟩
  · rintro (⟨hA, hB⟩ | ⟨hA, hC⟩)
    · exact ⟨hA, Or.inl hB⟩
    · exact ⟨hA, Or.inr hC⟩
-- BOOK: end set-distrib

end Handbook.C16
