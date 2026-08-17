/- 第32章 位相空間論
   32.3 filter 再訪 — 近傍系と収束の統一理論 -/
import Mathlib

namespace Handbook.C32

open Topology Filter

-- BOOK: begin filter-axioms
-- フィルタの3公理: 全体を含む・上に閉じる・共通部分で閉じる
example (l : Filter ℕ) : Set.univ ∈ l :=
  l.univ_sets

example (l : Filter ℕ) (s t : Set ℕ) (hs : s ∈ l) (h : s ⊆ t) :
    t ∈ l :=
  l.sets_of_superset hs h

example (l : Filter ℕ) (s t : Set ℕ) (hs : s ∈ l) (ht : t ∈ l) :
    s ∩ t ∈ l :=
  l.inter_sets hs ht
-- BOOK: end filter-axioms

-- BOOK: begin filter-nhds
-- 近傍系 𝓝 x: 「x を内側に含む開集合を含む集合」の族
example (X : Type) [TopologicalSpace X] (x : X) (s : Set X) :
    s ∈ 𝓝 x ↔ ∃ t ⊆ s, IsOpen t ∧ x ∈ t :=
  mem_nhds_iff

-- 連続性は「各点で近傍を近傍へ送る」と言い換えられる
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Continuous f ↔ ∀ x, ContinuousAt f x :=
  continuous_iff_continuousAt
-- BOOK: end filter-nhds

-- BOOK: begin filter-tendsto
-- 数列の極限の ε-N 定義は Tendsto u atTop (𝓝 a) と同値
example (u : ℕ → ℝ) (a : ℝ) :
    Tendsto u atTop (𝓝 a)
      ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε :=
  Metric.tendsto_atTop

-- 極限の合成則も1行。ε-δ の入れ子計算は現れない
example (X Y Z : Type) (f : X → Y) (g : Y → Z)
    (a : Filter X) (b : Filter Y) (c : Filter Z)
    (hf : Tendsto f a b) (hg : Tendsto g b c) :
    Tendsto (g ∘ f) a c :=
  hg.comp hf
-- BOOK: end filter-tendsto

end Handbook.C32
