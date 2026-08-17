/- 第17章 実数と数列の極限
   17.8 部分列 / 17.9 Cauchy 列と完備性 -/
import Mathlib

open Filter Topology

namespace Handbook.C17

-- BOOK: begin subseq-def
-- 部分列は添字を狭義単調な φ : ℕ → ℕ で拾ったもの。
-- φ が狭義単調なら φ n → ∞ が自動で従う
#check @StrictMono.tendsto_atTop

-- 収束列の部分列は、同じ極限へ収束する
example (a : ℕ → ℝ) (L : ℝ) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (h : Tendsto a atTop (𝓝 L)) :
    Tendsto (a ∘ φ) atTop (𝓝 L) :=
  h.comp hφ.tendsto_atTop
-- BOOK: end subseq-def

-- BOOK: begin conv-bdd
-- 収束列は有界。値域が上に有界であることが直接出る
example (a : ℕ → ℝ) (L : ℝ) (h : Tendsto a atTop (𝓝 L)) :
    BddAbove (Set.range a) :=
  h.bddAbove_range
-- BOOK: end conv-bdd

-- BOOK: begin cauchy-iff
-- Cauchy 列の ε-N 版。極限値 L が式に現れないのが要点
#check @Metric.cauchySeq_iff

-- 収束すれば Cauchy。逆向きには完備性が要る
example (a : ℕ → ℝ) (L : ℝ) (h : Tendsto a atTop (𝓝 L)) :
    CauchySeq a :=
  h.cauchySeq
-- BOOK: end cauchy-iff

-- BOOK: begin cauchy-geom
-- 差が等比級数で押さえられれば Cauchy。縮小写像の判定に使う
#check @cauchySeq_of_le_geometric
-- BOOK: end cauchy-geom

end Handbook.C17
