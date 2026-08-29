/- Chapter 17: Real numbers and limits of sequences
   17.7 Subsequences
   17.9 Cauchy sequences -/
import Mathlib

open Filter Topology

namespace Handbook.C17

-- BOOK: begin subseq-bdd
-- A convergent sequence is bounded; boundedness of the range
-- comes out directly
example (a : ℕ → ℝ) (L : ℝ) (h : Tendsto a atTop (𝓝 L)) :
    BddAbove (Set.range a) :=
  h.bddAbove_range
-- BOOK: end subseq-bdd

-- BOOK: begin subseq-def
-- A subsequence picks indices along a strictly monotone φ : ℕ → ℕ.
-- If φ is strictly monotone then φ n → ∞ follows automatically
#check @StrictMono.tendsto_atTop

-- A subsequence of a convergent sequence converges to the same limit
example (a : ℕ → ℝ) (L : ℝ) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (h : Tendsto a atTop (𝓝 L)) :
    Tendsto (a ∘ φ) atTop (𝓝 L) :=
  h.comp hφ.tendsto_atTop
-- BOOK: end subseq-def

-- BOOK: begin subseq-cauchy
-- The ε-N form of a Cauchy sequence; the point is that
-- no limit L appears
#check @Metric.cauchySeq_iff

-- Convergent implies Cauchy; the converse needs completeness
example (a : ℕ → ℝ) (L : ℝ) (h : Tendsto a atTop (𝓝 L)) :
    CauchySeq a :=
  h.cauchySeq
-- BOOK: end subseq-cauchy

-- BOOK: begin subseq-geometric
-- Differences bounded by a geometric series give a Cauchy sequence;
-- used for the contraction mapping test
#check @cauchySeq_of_le_geometric
-- BOOK: end subseq-geometric

end Handbook.C17
