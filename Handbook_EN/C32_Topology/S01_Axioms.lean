/- English edition source: Handbook/C32_Topology/S01_Axioms.lean. -/
import Mathlib

namespace Handbook.C32

open Topology

-- BOOK: begin topo-axioms
-- The three axioms of a topology: the intersection of two open sets
-- is open, and an arbitrary union of open sets is open
example (X : Type) [TopologicalSpace X] :
    IsOpen (Set.univ : Set X) :=
  isOpen_univ

example (X : Type) [TopologicalSpace X] (s t : Set X)
    (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t) :=
  hs.inter ht

-- Unions are arbitrary: if every member of the family F is open,
-- so is their union
example (X : Type) [TopologicalSpace X] (F : Set (Set X))
    (hF : ∀ t ∈ F, IsOpen t) : IsOpen (⋃₀ F) :=
  isOpen_sUnion hF
-- BOOK: end topo-axioms

-- BOOK: begin topo-discrete
-- The discrete topology: every subset is open
example (X : Type) [TopologicalSpace X] [DiscreteTopology X]
    (s : Set X) : IsOpen s :=
  isOpen_discrete s

-- the bottom ⊥ of the lattice always carries DiscreteTopology
example (X : Type) : @DiscreteTopology X ⊥ :=
  discreteTopology_bot X
-- BOOK: end topo-discrete

-- BOOK: begin topo-indiscrete
-- The indiscrete topology sits at the top ⊤ of the lattice:
-- only the empty set and the whole space are open
example (X : Type) (s : Set X) :
    IsOpen[⊤] s ↔ s = ∅ ∨ s = Set.univ :=
  TopologicalSpace.isOpen_top_iff s

-- In the usual topology of ℝ the open intervals are the basic
-- open sets
example (a b : ℝ) : IsOpen (Set.Ioo a b) :=
  isOpen_Ioo
-- BOOK: end topo-indiscrete

end Handbook.C32
