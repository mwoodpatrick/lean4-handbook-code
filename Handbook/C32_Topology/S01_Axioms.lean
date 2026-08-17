/- 第32章 位相空間論
   32.1 位相の公理と例 -/
import Mathlib

namespace Handbook.C32

open Topology

-- BOOK: begin topo-axioms
-- 位相の3公理: 全体が開・2つの共通部分が開・任意個の合併が開
example (X : Type) [TopologicalSpace X] :
    IsOpen (Set.univ : Set X) :=
  isOpen_univ

example (X : Type) [TopologicalSpace X] (s t : Set X)
    (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t) :=
  hs.inter ht

-- 合併は「任意個」— 集合族 F のすべてが開なら和集合も開
example (X : Type) [TopologicalSpace X] (F : Set (Set X))
    (hF : ∀ t ∈ F, IsOpen t) : IsOpen (⋃₀ F) :=
  isOpen_sUnion hF
-- BOOK: end topo-axioms

-- BOOK: begin topo-discrete
-- 離散位相: すべての部分集合が開。mathlib では ⊥ がこれ
example (X : Type) [TopologicalSpace X] [DiscreteTopology X]
    (s : Set X) : IsOpen s :=
  isOpen_discrete s

-- ⊥ には常に DiscreteTopology が付く(束の下端が最も細かい)
example (X : Type) : @DiscreteTopology X ⊥ :=
  discreteTopology_bot X
-- BOOK: end topo-discrete

-- BOOK: begin topo-indiscrete
-- 密着位相は束の上端 ⊤。開集合は空集合と全体だけ
example (X : Type) (s : Set X) :
    IsOpen[⊤] s ↔ s = ∅ ∨ s = Set.univ :=
  TopologicalSpace.isOpen_top_iff s

-- ℝ の通常の位相では開区間が開集合の基本形
example (a b : ℝ) : IsOpen (Set.Ioo a b) :=
  isOpen_Ioo
-- BOOK: end topo-indiscrete

end Handbook.C32
