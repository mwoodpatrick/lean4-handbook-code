/- English edition source: Handbook/C33_Measure/S02_Volume.lean. -/
import Mathlib

namespace Handbook.C33

open MeasureTheory

-- BOOK: begin measure-def
-- The Lebesgue measure: the measure of an interval is its length
example : volume (Set.Icc (0 : ℝ) 3) = 3 := by
  rw [Real.volume_Icc]
  norm_num

-- A finite set has measure zero (a precise form of “points have no
-- length”).
example : volume ({1, 2, 3} : Set ℝ) = 0 :=
  (Set.toFinite _).measure_zero volume
-- BOOK: end measure-def

-- BOOK: begin measure-props
-- Basic properties of a measure: the empty set has measure zero,
-- and inclusion gives an inequality of measures
example (α : Type) [MeasurableSpace α] (μ : Measure α) :
    μ ∅ = 0 :=
  measure_empty

example (α : Type) [MeasurableSpace α] (μ : Measure α) (s t : Set α)
    (h : s ⊆ t) : μ s ≤ μ t :=
  measure_mono h
-- BOOK: end measure-props

-- BOOK: begin measure-additive
-- Countable additivity: the measure of a union of pairwise disjoint
-- sets is the sum of the measures
example (α : Type) [MeasurableSpace α] (μ : Measure α)
    (f : ℕ → Set α) (hd : Pairwise (Function.onFun Disjoint f))
    (hm : ∀ i, MeasurableSet (f i)) :
    μ (⋃ i, f i) = ∑' i, μ (f i) :=
  measure_iUnion hd hm
-- BOOK: end measure-additive

-- BOOK: begin measure-subadditive
-- Subadditivity: overlaps are allowed, giving an upper bound from a
-- cover
example (α : Type) [MeasurableSpace α] (μ : Measure α)
    (s : ℕ → Set α) : μ (⋃ i, s i) ≤ ∑' i, μ (s i) :=
  measure_iUnion_le s

-- a countable union of null sets is still null
example (α : Type) [MeasurableSpace α] (μ : Measure α)
    (s : ℕ → Set α) (h : ∀ i, μ (s i) = 0) : μ (⋃ i, s i) = 0 :=
  measure_iUnion_null h
-- BOOK: end measure-subadditive

-- BOOK: begin volume-interval
-- The Lebesgue measure of an interval is its length: the strict
-- definition of "length" on ℝ
example (a b : ℝ) : volume (Set.Icc a b) = ENNReal.ofReal (b - a) :=
  Real.volume_Icc

-- the same holds for an open interval; the endpoints do not
-- contribute to the measure
example (a b : ℝ) : volume (Set.Ioo a b) = ENNReal.ofReal (b - a) :=
  Real.volume_Ioo
-- BOOK: end volume-interval

end Handbook.C33
