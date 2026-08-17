/- 第17章 実数と数列の極限
   17.7 発散と無限大 -/
import Mathlib

open Filter Topology

namespace Handbook.C17

-- BOOK: begin diverge-def
-- 「∞ へ発散」は行き先のフィルタを atTop にするだけで書ける
#check @tendsto_atTop_atTop

-- 自然数を実数と見た列 n ↦ (n : ℝ) は ∞ へ発散する
example : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop
-- BOOK: end diverge-def

-- BOOK: begin diverge-not-conv
-- ∞ へ発散する列は、どんな実数にも収束しない
example (a : ℕ → ℝ) (h : Tendsto a atTop atTop) (L : ℝ) :
    ¬ Tendsto a atTop (𝓝 L) :=
  not_tendsto_nhds_of_tendsto_atTop h L
-- BOOK: end diverge-not-conv

-- BOOK: begin geom-zero
-- 0 ≤ r < 1 なら r^n → 0。等比数列の収束
example (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) :
    Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1
-- BOOK: end geom-zero

-- BOOK: begin sup-calc
-- 閉区間の上限は右端。上限が集合に属する場合である
example (a b : ℝ) (h : a ≤ b) : sSup (Set.Icc a b) = b :=
  csSup_Icc h
-- BOOK: end sup-calc

end Handbook.C17
