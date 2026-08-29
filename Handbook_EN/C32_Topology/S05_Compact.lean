/- English edition source: Handbook/C32_Topology/S05_Compact.lean. -/
import Mathlib

namespace Handbook.C32

-- BOOK: begin compact-cover
-- The definition of compactness: every open cover has a finite
-- subcover.
example (X : Type) [TopologicalSpace X] (s : Set X)
    (hs : IsCompact s) (U : ℕ → Set X) (hU : ∀ i, IsOpen (U i))
    (hsub : s ⊆ ⋃ i, U i) :
    ∃ t : Finset ℕ, s ⊆ ⋃ i ∈ t, U i :=
  hs.elim_finite_subcover U hU hsub
-- BOOK: end compact-cover

-- BOOK: begin compact-image
-- The compact set of continuous images is compact (the heart of the
-- maximum value)
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (s : Set X) (hs : IsCompact s)
    (hf : Continuous f) : IsCompact (f '' s) :=
  hs.image hf

-- The closed section is compact (Heine Borel). Chapter 18
example (a b : ℝ) : IsCompact (Set.Icc a b) :=
  isCompact_Icc
-- BOOK: end compact-image

-- BOOK: begin compact-max
-- Maximum value theorem: a continuous function on a compact set attains
-- its maximum.
example (s : Set ℝ) (hs : IsCompact s) (hne : s.Nonempty)
    (f : ℝ → ℝ) (hf : ContinuousOn f s) :
    ∃ x ∈ s, IsMaxOn f s x :=
  hs.exists_isMaxOn hne hf
-- BOOK: end compact-max

-- BOOK: begin tychonoff
-- Tychonoff’s theorem: an arbitrary product of compact spaces is
-- compact.
example (ι : Type) (X : ι → Type) [∀ i, TopologicalSpace (X i)]
    (s : ∀ i, Set (X i)) (hs : ∀ i, IsCompact (s i)) :
    IsCompact {x : ∀ i, X i | ∀ i, x i ∈ s i} :=
  isCompact_pi_infinite hs
-- BOOK: end tychonoff

-- BOOK: begin compact-fip
-- Finite-intersection property: a decreasing sequence of nonempty
-- compact closed sets has nonempty intersection.
example (X : Type) [TopologicalSpace X] (t : ℕ → Set X)
    (hdir : Directed (· ⊇ ·) t) (hne : ∀ i, (t i).Nonempty)
    (hcp : ∀ i, IsCompact (t i)) (hcl : ∀ i, IsClosed (t i)) :
    (⋂ i, t i).Nonempty :=
  IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    t hdir hne hcp hcl
-- BOOK: end compact-fip

end Handbook.C32
