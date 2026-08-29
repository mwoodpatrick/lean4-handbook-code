/- English edition source: Handbook/C32_Topology/S07_Separation.lean. -/
import Mathlib

namespace Handbook.C32

open Topology Filter

-- BOOK: begin t2-unique
-- In a Hausdorff (T2) space the limit is unique
example (X : Type) [TopologicalSpace X] [T2Space X]
    (f : ℕ → X) (a b : X)
    (ha : Tendsto f atTop (𝓝 a))
    (hb : Tendsto f atTop (𝓝 b)) : a = b :=
  tendsto_nhds_unique ha hb
-- BOOK: end t2-unique

-- BOOK: begin t1-singleton
-- In a T1 space singletons are closed; T2 implies T1
example (X : Type) [TopologicalSpace X] [T1Space X] (x : X) :
    IsClosed ({x} : Set X) :=
  isClosed_singleton

example (X : Type) [TopologicalSpace X] [T2Space X] : T1Space X :=
  T2Space.t1Space
-- BOOK: end t1-singleton

-- BOOK: begin t2-compact-closed
-- The effect of T2: a compact set is automatically closed
example (X : Type) [TopologicalSpace X] [T2Space X] (s : Set X)
    (hs : IsCompact s) : IsClosed s :=
  hs.isClosed
-- BOOK: end t2-compact-closed

-- BOOK: begin separation-cont
-- Two points sent to different values by a continuous map can be
-- separated by open sets
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] (f : X → Y) (hf : Continuous f) (x y : X)
    (h : f x ≠ f y) :
    ∃ u v, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v :=
  separated_by_continuous hf h
-- BOOK: end separation-cont

-- BOOK: begin urysohn
-- Urysohn's lemma: in a normal space, disjoint closed sets are
-- separated by a continuous function
example (X : Type) [TopologicalSpace X] [NormalSpace X] (s t : Set X)
    (hs : IsClosed s) (ht : IsClosed t) (hst : Disjoint s t) :
    ∃ f : C(X, ℝ), Set.EqOn f 0 s ∧ Set.EqOn f 1 t
      ∧ ∀ x, f x ∈ Set.Icc (0 : ℝ) 1 :=
  exists_continuous_zero_one_of_isClosed hs ht hst
-- BOOK: end urysohn

end Handbook.C32
