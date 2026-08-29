/- English edition source: Handbook/C28_Foundations/S01_ZFC.lean. -/
import Mathlib

namespace Handbook.C28

-- BOOK: begin zfc
-- ZFC set theory itself is one of mathlib's objects
#check ZFSet     -- ZFC set mould
#check Ordinal   -- Order number
#check Cardinal  -- Number
-- BOOK: end zfc

-- BOOK: begin zfc-axioms
-- In ZFSet, extensionality holds as a theorem: sets with the same
-- elements are equal.
example (x y : ZFSet) (h : ∀ z, z ∈ x ↔ z ∈ y) : x = y :=
  ZFSet.ext h

-- nothing belongs to the empty set
example (z : ZFSet) : z ∉ (∅ : ZFSet) := ZFSet.notMem_empty z
-- BOOK: end zfc-axioms

-- BOOK: begin transfinite
-- Transfinite induction advances to an ordinal from the hypothesis that
-- the claim holds for every smaller ordinal.
-- (The general form holds for any well-founded order; the ordinals
-- are the representative example.)
example {p : Ordinal → Prop} (i : Ordinal)
    (h : ∀ j, (∀ k < j, p k) → p j) : p i :=
  WellFoundedLT.induction i h
-- BOOK: end transfinite

-- BOOK: begin cantor
-- Cantor's theorem (cardinal version): a < 2^a.
-- The power set is always strictly larger.
example (a : Cardinal) : a < 2 ^ a := Cardinal.cantor a

-- Infinite cardinal arithmetic: κ + κ = κ and κ · κ = κ for κ ≥ ℵ₀
example (κ : Cardinal) (h : Cardinal.aleph0 ≤ κ) : κ * κ = κ :=
  Cardinal.mul_eq_self h
-- BOOK: end cantor

-- BOOK: begin continuum
-- The cardinality of the reals is the continuum c = 2^ℵ₀,
-- strictly larger than that of ℕ
example : Cardinal.mk ℝ = 2 ^ Cardinal.aleph0 := by
  rw [Cardinal.mk_real, Cardinal.continuum]

-- hence the reals are uncountable (unlike ℕ)
example : ¬ (Set.univ : Set ℝ).Countable :=
  Cardinal.not_countable_real
-- BOOK: end continuum

-- BOOK: begin diaconescu
-- Diaconescu's theorem: excluded middle follows from the axiom of
-- choice. mathlib's Classical.em is proved along this route.
#check @Classical.em

-- so mathlib works in classical logic
example (p : Prop) : p ∨ ¬ p := Classical.em p
-- BOOK: end diaconescu

end Handbook.C28
