/- 第16章 集合と写像 — 数学の言語
   16.2 集合演算と包含 -/
import Mathlib

namespace Handbook.C16

open Set

-- BOOK: begin set-ops
example (A B : Set ℕ) : A ∩ B ⊆ A := inter_subset_left

example (A B : Set ℕ) : A ⊆ A ∪ B := subset_union_left

-- ド・モルガンの法則
example (A B : Set ℕ) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := compl_union A B
-- BOOK: end set-ops

-- BOOK: begin set-antisymm
-- 集合の相等は両向きの包含(外延性)
example (A B : Set ℕ) (h1 : A ⊆ B) (h2 : B ⊆ A) : A = B :=
  Subset.antisymm h1 h2

-- 要素を取って示す標準形
example (A B C : Set ℕ) (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C := by
  intro x hx
  exact h2 (h1 hx)
-- BOOK: end set-antisymm

-- BOOK: begin set-distrib
-- 分配律: ext で要素を取り、あとは第5章の論理の証明に落ちる
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
