/- 第32章 位相空間論
   32.4 閉包・内部・境界 -/
import Mathlib

namespace Handbook.C32

-- BOOK: begin closure-min
-- 閉包は「S を含む最小の閉集合」— 2つの補題がその普遍性
example (X : Type) [TopologicalSpace X] (s : Set X) :
    s ⊆ closure s :=
  subset_closure

example (X : Type) [TopologicalSpace X] (s t : Set X)
    (h₁ : s ⊆ t) (h₂ : IsClosed t) : closure s ⊆ t :=
  closure_minimal h₁ h₂

-- 閉集合であることと閉包が自分自身であることは同値
example (X : Type) [TopologicalSpace X] (s : Set X)
    (hs : IsClosed s) : closure s = s :=
  hs.closure_eq
-- BOOK: end closure-min

-- BOOK: begin closure-mem
-- 「x が閉包に属する」⇔「x のどの開近傍も S と交わる」
example (X : Type) [TopologicalSpace X] (x : X) (s : Set X) :
    x ∈ closure s ↔ ∀ o, IsOpen o → x ∈ o → (o ∩ s).Nonempty :=
  mem_closure_iff
-- BOOK: end closure-mem

-- BOOK: begin interior-frontier
-- 内部は「S に含まれる最大の開集合」— 閉包と双対の普遍性
example (X : Type) [TopologicalSpace X] (s : Set X) :
    interior s ⊆ s :=
  interior_subset

example (X : Type) [TopologicalSpace X] (s t : Set X)
    (h₁ : t ⊆ s) (h₂ : IsOpen t) : t ⊆ interior s :=
  interior_maximal h₁ h₂

-- 境界は「閉包と補集合の閉包の共通部分」
example (X : Type) [TopologicalSpace X] (s : Set X) :
    frontier s = closure s ∩ closure sᶜ :=
  frontier_eq_closure_inter_closure
-- BOOK: end interior-frontier

end Handbook.C32
