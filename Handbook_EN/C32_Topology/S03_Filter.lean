/- English edition source: Handbook/C32_Topology/S03_Filter.lean. -/
import Mathlib

namespace Handbook.C32

open Topology Filter

-- BOOK: begin filter-axioms
-- The three axioms of a filter: it contains the whole set,
-- is upward closed, and is closed under intersection
example (l : Filter ℕ) : Set.univ ∈ l :=
  l.univ_sets

example (l : Filter ℕ) (s t : Set ℕ) (hs : s ∈ l) (h : s ⊆ t) :
    t ∈ l :=
  l.sets_of_superset hs h

example (l : Filter ℕ) (s t : Set ℕ) (hs : s ∈ l) (ht : t ∈ l) :
    s ∩ t ∈ l :=
  l.inter_sets hs ht
-- BOOK: end filter-axioms

-- BOOK: begin filter-nhds
-- The neighborhood filter 𝓝 x: the sets containing an open set
-- that contains x
example (X : Type) [TopologicalSpace X] (x : X) (s : Set X) :
    s ∈ 𝓝 x ↔ ∃ t ⊆ s, IsOpen t ∧ x ∈ t :=
  mem_nhds_iff

-- Continuity is restated as sending neighborhoods to neighborhoods
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Continuous f ↔ ∀ x, ContinuousAt f x :=
  continuous_iff_continuousAt
-- BOOK: end filter-nhds

-- BOOK: begin filter-tendsto
-- The ε-N definition for a sequence is equivalent to
-- Tendsto u atTop (𝓝 a)
example (u : ℕ → ℝ) (a : ℝ) :
    Tendsto u atTop (𝓝 a)
      ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε :=
  Metric.tendsto_atTop

-- Composition of limits is also one line; no nested ε-δ calculation
-- appears.
example (X Y Z : Type) (f : X → Y) (g : Y → Z)
    (a : Filter X) (b : Filter Y) (c : Filter Z)
    (hf : Tendsto f a b) (hg : Tendsto g b c) :
    Tendsto (g ∘ f) a c :=
  hg.comp hf
-- BOOK: end filter-tendsto

end Handbook.C32
