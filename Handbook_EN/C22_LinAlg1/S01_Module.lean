/- Chapter 22: Linear algebra I
   22.1 Vector spaces and subspaces -/
import Mathlib

namespace Handbook.C22

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

-- BOOK: begin module-axioms
-- The axioms of a vector space are usable as theorems of Module
example (a : ℝ) (v w : V) : a • (v + w) = a • v + a • w :=
  smul_add a v w

example (v : V) : (0 : ℝ) • v = 0 := zero_smul ℝ v
-- BOOK: end module-axioms

-- BOOK: begin submodule
-- A Submodule is a subset closed under sums and scalar multiples
example (W : Submodule ℝ V) (v w : V)
    (hv : v ∈ W) (hw : w ∈ W) : v + w ∈ W :=
  W.add_mem hv hw

example (W : Submodule ℝ V) (a : ℝ) (v : V) (hv : v ∈ W) :
    a • v ∈ W :=
  W.smul_mem a hv
-- BOOK: end submodule

-- BOOK: begin span-mem
-- A generator always belongs to the subspace it generates
example (S : Set V) (v : V) (hv : v ∈ S) :
    v ∈ Submodule.span ℝ S :=
  Submodule.subset_span hv

-- to show span S ≤ W it is enough that each element of S is in W
example (S : Set V) (W : Submodule ℝ V) (h : S ⊆ W) :
    Submodule.span ℝ S ≤ W :=
  Submodule.span_le.mpr h
-- BOOK: end span-mem

end Handbook.C22
