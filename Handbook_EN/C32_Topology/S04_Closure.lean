/- English edition source: Handbook/C32_Topology/S04_Closure.lean. -/
import Mathlib

namespace Handbook.C32

-- BOOK: begin closure-min
-- The closure is the smallest closed set containing S; the two
-- lemmas give its universal property
example (X : Type) [TopologicalSpace X] (s : Set X) :
    s ⊆ closure s :=
  subset_closure

example (X : Type) [TopologicalSpace X] (s t : Set X)
    (h₁ : s ⊆ t) (h₂ : IsClosed t) : closure s ⊆ t :=
  closure_minimal h₁ h₂

-- A set is closed exactly when it equals its own closure
example (X : Type) [TopologicalSpace X] (s : Set X)
    (hs : IsClosed s) : closure s = s :=
  hs.closure_eq
-- BOOK: end closure-min

-- BOOK: begin closure-mem
-- x belongs to the closure ⟺ every open set containing x meets S
example (X : Type) [TopologicalSpace X] (x : X) (s : Set X) :
    x ∈ closure s ↔ ∀ o, IsOpen o → x ∈ o → (o ∩ s).Nonempty :=
  mem_closure_iff
-- BOOK: end closure-mem

-- BOOK: begin interior-frontier
-- The interior is the largest open set inside S: the universal
-- property dual to the closure
example (X : Type) [TopologicalSpace X] (s : Set X) :
    interior s ⊆ s :=
  interior_subset

example (X : Type) [TopologicalSpace X] (s t : Set X)
    (h₁ : t ⊆ s) (h₂ : IsOpen t) : t ⊆ interior s :=
  interior_maximal h₁ h₂

-- The frontier is the intersection of the closure with the closure
-- of the complement
example (X : Type) [TopologicalSpace X] (s : Set X) :
    frontier s = closure s ∩ closure sᶜ :=
  frontier_eq_closure_inter_closure
-- BOOK: end interior-frontier

end Handbook.C32
