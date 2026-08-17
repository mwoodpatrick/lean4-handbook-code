/- 第17章 実数と数列の極限
   17.6 単調収束定理 / 17.7 Cauchy 列と完備性 -/
import Mathlib

namespace Handbook.C17

open Filter Topology

-- BOOK: begin mct
-- 単調収束定理: 上に有界な単調増加列は収束する
example (a : ℕ → ℝ) (hmono : Monotone a)
    (hbdd : BddAbove (Set.range a)) :
    ∃ L, Tendsto a atTop (𝓝 L) :=
  ⟨_, tendsto_atTop_ciSup hmono hbdd⟩
-- BOOK: end mct

-- BOOK: begin cauchy
-- 完備性: コーシー列は(極限を言い当てなくても)収束する
example (a : ℕ → ℝ) (h : CauchySeq a) :
    ∃ L, Tendsto a atTop (𝓝 L) :=
  cauchySeq_tendsto_of_complete h
-- BOOK: end cauchy

-- BOOK: begin bolzano
-- Bolzano–Weierstrass: 有界列は収束する部分列を持つ
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
-- BOOK: end bolzano

end Handbook.C17
