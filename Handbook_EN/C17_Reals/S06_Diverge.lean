/- Chapter 17: Real numbers and limits of sequences
   17.2 Suprema of intervals
   17.6 Divergence and infinity -/
import Mathlib

open Filter Topology

namespace Handbook.C17

-- BOOK: begin diverge-sup-icc
-- The supremum of a closed interval is its right endpoint;
-- here it belongs to the set
example (a b : ℝ) (h : a ≤ b) : sSup (Set.Icc a b) = b :=
  csSup_Icc h
-- BOOK: end diverge-sup-icc

-- BOOK: begin diverge-atTop
-- "diverges to ∞" is written by switching the target filter to atTop
#check @tendsto_atTop_atTop

-- the sequence n ↦ (n : ℝ) of naturals seen as reals diverges to ∞
example : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop
-- BOOK: end diverge-atTop

-- BOOK: begin diverge-not-nhds
-- a sequence diverging to ∞ converges to no real number
example (a : ℕ → ℝ) (h : Tendsto a atTop atTop) (L : ℝ) :
    ¬ Tendsto a atTop (𝓝 L) :=
  not_tendsto_nhds_of_tendsto_atTop h L
-- BOOK: end diverge-not-nhds

-- BOOK: begin diverge-geom
-- if 0 ≤ r < 1 then r^n → 0: convergence of a geometric sequence
example (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) :
    Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1
-- BOOK: end diverge-geom

end Handbook.C17
