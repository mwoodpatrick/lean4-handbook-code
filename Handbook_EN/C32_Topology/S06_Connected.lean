/- English edition source: Handbook/C32_Topology/S06_Connected.lean. -/
import Mathlib

namespace Handbook.C32

-- BOOK: begin connected-image
-- The continuous image of a connected set is connected
-- (the topological body of the intermediate value theorem)
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (s : Set X) (hs : IsConnected s)
    (hf : ContinuousOn f s) : IsConnected (f '' s) :=
  hs.image f hf
-- BOOK: end connected-image

-- BOOK: begin connected-icc
-- An interval is connected. This lemma and the one above give the
-- intermediate value theorem.
example (a b : ℝ) : IsPreconnected (Set.Icc a b) :=
  isPreconnected_Icc
-- BOOK: end connected-icc

-- BOOK: begin ivt
-- Meaning: all values between f a and f b appear in the image
example (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) :
    Set.Icc (f a) (f b) ⊆ f '' Set.Icc a b :=
  intermediate_value_Icc hab hf

-- Worked example: x³ + x − 1 has a zero between 0 and 1
example : ∃ x ∈ Set.Icc (0 : ℝ) 1, x ^ 3 + x - 1 = 0 := by
  have hc : ContinuousOn (fun x : ℝ => x ^ 3 + x - 1)
      (Set.Icc 0 1) := by fun_prop
  have h := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hc
  have h0 : (0 : ℝ) ∈ Set.Icc ((0:ℝ) ^ 3 + 0 - 1)
      ((1:ℝ) ^ 3 + 1 - 1) := by norm_num
  obtain ⟨x, hx, hfx⟩ := h h0
  exact ⟨x, hx, hfx⟩
-- BOOK: end ivt

-- BOOK: begin connected-component
-- The connected component: the largest connected set containing x.
-- Components divide the space into pieces.
example (X : Type) [TopologicalSpace X] (x : X) :
    IsConnected (connectedComponent x) :=
  isConnected_connectedComponent

-- Path-connected implies connected (the converse fails in general)
example (X : Type) [TopologicalSpace X] (s : Set X)
    (hs : IsPathConnected s) : IsConnected s :=
  hs.isConnected
-- BOOK: end connected-component

end Handbook.C32
