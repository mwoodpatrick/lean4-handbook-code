/- 第32章 位相空間論
   32.7 分離公理(T₀〜T₄) -/
import Mathlib

namespace Handbook.C32

open Topology Filter

-- BOOK: begin t2-unique
-- ハウスドルフ空間(T₂)では極限が一意に定まる
example (X : Type) [TopologicalSpace X] [T2Space X]
    (f : ℕ → X) (a b : X)
    (ha : Tendsto f atTop (𝓝 a))
    (hb : Tendsto f atTop (𝓝 b)) : a = b :=
  tendsto_nhds_unique ha hb
-- BOOK: end t2-unique

-- BOOK: begin t1-singleton
-- T₁ 空間では1点集合が閉。T₂ ならば T₁ が従う
example (X : Type) [TopologicalSpace X] [T1Space X] (x : X) :
    IsClosed ({x} : Set X) :=
  isClosed_singleton

example (X : Type) [TopologicalSpace X] [T2Space X] : T1Space X :=
  T2Space.t1Space
-- BOOK: end t1-singleton

-- BOOK: begin t2-compact-closed
-- T₂ の効き目: コンパクト集合が自動的に閉集合になる
example (X : Type) [TopologicalSpace X] [T2Space X] (s : Set X)
    (hs : IsCompact s) : IsClosed s :=
  hs.isClosed
-- BOOK: end t2-compact-closed

-- BOOK: begin separation-cont
-- 値の異なる2点は、連続写像があれば開集合で引き離せる
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] (f : X → Y) (hf : Continuous f) (x y : X)
    (h : f x ≠ f y) :
    ∃ u v, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v :=
  separated_by_continuous hf h
-- BOOK: end separation-cont

-- BOOK: begin urysohn
-- ウリゾーンの補題: 正規空間では交わらない閉集合を関数で隔てられる
example (X : Type) [TopologicalSpace X] [NormalSpace X] (s t : Set X)
    (hs : IsClosed s) (ht : IsClosed t) (hst : Disjoint s t) :
    ∃ f : C(X, ℝ), Set.EqOn f 0 s ∧ Set.EqOn f 1 t
      ∧ ∀ x, f x ∈ Set.Icc (0 : ℝ) 1 :=
  exists_continuous_zero_one_of_isClosed hs ht hst
-- BOOK: end urysohn

end Handbook.C32
