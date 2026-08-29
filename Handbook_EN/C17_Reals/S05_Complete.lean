/- Chapter 17: Real numbers and limits of sequences
   17.8 Monotone convergence and Bolzano--Weierstrass
   17.9 Cauchy sequences and completeness -/
import Mathlib

open Filter Topology Bornology

namespace Handbook.C17

-- BOOK: begin complete-monotone
-- Monotone convergence: a monotone increasing sequence
-- bounded above converges
example (a : ℕ → ℝ) (hmono : Monotone a)
    (hbdd : BddAbove (Set.range a)) :
    ∃ L, Tendsto a atTop (𝓝 L) :=
  ⟨_, tendsto_atTop_ciSup hmono hbdd⟩
-- BOOK: end complete-monotone

-- BOOK: begin complete-bw
-- Bolzano--Weierstrass: a bounded sequence has a convergent subsequence
example (a : ℕ → ℝ) (hbdd : ∃ C, ∀ n, |a n| ≤ C) :
    ∃ (L : ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
        Tendsto (a ∘ φ) atTop (𝓝 L) := by
  obtain ⟨C, hC⟩ := hbdd
  have hb : Bornology.IsBounded (Set.range a) := by
    rw [isBounded_iff_bddBelow_bddAbove]
    constructor
    · exact ⟨-C, by rintro _ ⟨n, rfl⟩; linarith [abs_le.1 (hC n)]⟩
    · exact ⟨C, by rintro _ ⟨n, rfl⟩; linarith [abs_le.1 (hC n)]⟩
  have hmem : ∀ n, a n ∈ Set.range a := fun n => ⟨n, rfl⟩
  obtain ⟨L, -, φ, hφ, hL⟩ := tendsto_subseq_of_bounded hb hmem
  exact ⟨L, φ, hφ, hL⟩
-- BOOK: end complete-bw

-- BOOK: begin complete-cauchy
-- Completeness: a Cauchy sequence converges (without naming the limit)
example (a : ℕ → ℝ) (h : CauchySeq a) :
    ∃ L, Tendsto a atTop (𝓝 L) :=
  cauchySeq_tendsto_of_complete h
-- BOOK: end complete-cauchy

end Handbook.C17
