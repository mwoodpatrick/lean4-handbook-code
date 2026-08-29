/- English edition source: Handbook/C18_Continuity/S04_Limits.lean. -/
import Mathlib

open Filter Topology

namespace Handbook.C18

-- BOOK: begin flimit-def
-- ε-δ translation of a function limit: for each ε one may choose a δ
#check @Metric.tendsto_nhds_nhds

-- lim_{x→2} (3x + 1) = 7
example : Tendsto (fun x : ℝ => 3 * x + 1) (𝓝 2) (𝓝 7) := by
  have h : Continuous (fun x : ℝ => 3 * x + 1) := by fun_prop
  have := h.tendsto 2
  norm_num at this
  exact this
-- BOOK: end flimit-def

-- BOOK: begin flimit-punctured
-- 𝓝[≠] a is a “punctured neighborhood of a,” excluding x = a as in the
-- classical definition
#check @Metric.tendsto_nhdsWithin_nhds

-- A punctured limit. It is weaker than 𝓝 a and therefore easier to
-- satisfy.
example (f : ℝ → ℝ) (a L : ℝ) (h : Tendsto f (𝓝 a) (𝓝 L)) :
    Tendsto f (𝓝[≠] a) (𝓝 L) :=
  h.mono_left nhdsWithin_le_nhds
-- BOOK: end flimit-punctured

-- BOOK: begin flimit-alg
-- Arithmetic laws for limits. The source filter is arbitrary, so they
-- apply to sequences and functions.
#check @Filter.Tendsto.add

-- Only division requires the denominator’s limit to be nonzero
#check @Filter.Tendsto.div
-- BOOK: end flimit-alg

-- BOOK: begin onesided
-- A one-sided limit is continuity with the domain restricted to Ioi a
-- (the right side)
example (f : ℝ → ℝ) (a : ℝ) :
    ContinuousWithinAt f (Set.Ioi a) a ↔
      ContinuousWithinAt f (Set.Ici a) a :=
  continuousWithinAt_Ioi_iff_Ici
-- BOOK: end onesided

-- BOOK: begin seq-cont
-- Over ℝ, continuity is equivalent to “mapping convergent sequences to
-- convergent sequences”
example (f : ℝ → ℝ) (h : Continuous f) : SeqContinuous f :=
  continuous_iff_seqContinuous.mp h

-- Filter version: for countably generated filters, sequences suffice
-- for testing
#check @Filter.tendsto_iff_seq_tendsto
-- BOOK: end seq-cont

end Handbook.C18
