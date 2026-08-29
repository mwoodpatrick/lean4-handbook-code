/- English edition source: Handbook/C29_Groups/S01_Group.lean. -/
import Mathlib

namespace Handbook.C29

-- BOOK: begin group-axioms
-- The group tactic automatically closes group calculations from the
-- axioms.
example (G : Type) [Group G] (a b : G) :
    a * b * b⁻¹ = a := by group

example (G : Type) [Group G] (a b : G) :
    (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  mul_inv_rev a b
-- BOOK: end group-axioms

-- BOOK: begin subgroup
-- A subgroup: a subset closed under the operation and inverses
example (G : Type) [Group G] (H : Subgroup G) (a b : G)
    (ha : a ∈ H) (hb : b ∈ H) : a * b ∈ H :=
  H.mul_mem ha hb

example (G : Type) [Group G] (H : Subgroup G) (a : G)
    (ha : a ∈ H) : a⁻¹ ∈ H :=
  H.inv_mem ha
-- BOOK: end subgroup

-- BOOK: begin subgroup-closure
-- closure S is the smallest subgroup containing S;
-- every element of S belongs to it
example (G : Type) [Group G] (S : Set G) : S ⊆ Subgroup.closure S :=
  Subgroup.subset_closure

-- to show closure S ≤ H it is enough that S ⊆ H (minimality)
example (G : Type) [Group G] (S : Set G) (H : Subgroup G)
    (h : S ⊆ H) : Subgroup.closure S ≤ H :=
  (Subgroup.closure_le H).mpr h
-- BOOK: end subgroup-closure

-- BOOK: begin group-examples
-- Familiar examples: the integers form an additive group, and so does
-- ℤ/nℤ (Chapter 14).
example : AddGroup ℤ := inferInstance

example (n : ℕ) [NeZero n] : AddCommGroup (ZMod n) := inferInstance
-- BOOK: end group-examples

end Handbook.C29
