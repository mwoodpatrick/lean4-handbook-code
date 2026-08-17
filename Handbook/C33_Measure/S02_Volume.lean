/- 第33章 測度論とルベーグ積分
   33.3 測度とルベーグ測度 -/
import Mathlib

namespace Handbook.C33

open MeasureTheory

-- BOOK: begin measure-def
-- ルベーグ測度 volume。区間の測度は長さ
example : volume (Set.Icc (0 : ℝ) 3) = 3 := by
  rw [Real.volume_Icc]
  norm_num

-- 有限集合の測度はゼロ(「点には長さがない」の厳密化)
example : volume ({1, 2, 3} : Set ℝ) = 0 :=
  (Set.toFinite _).measure_zero volume
-- BOOK: end measure-def

-- BOOK: begin measure-props
-- 測度の基本性質: 空集合はゼロ、包含すれば大小も保たれる
example (α : Type) [MeasurableSpace α] (μ : Measure α) :
    μ ∅ = 0 :=
  measure_empty

example (α : Type) [MeasurableSpace α] (μ : Measure α) (s t : Set α)
    (h : s ⊆ t) : μ s ≤ μ t :=
  measure_mono h
-- BOOK: end measure-props

-- BOOK: begin measure-additive
-- 可算加法性: 互いに交わらない可測集合の合併の測度は総和
example (α : Type) [MeasurableSpace α] (μ : Measure α)
    (f : ℕ → Set α) (hd : Pairwise (Function.onFun Disjoint f))
    (hm : ∀ i, MeasurableSet (f i)) :
    μ (⋃ i, f i) = ∑' i, μ (f i) :=
  measure_iUnion hd hm
-- BOOK: end measure-additive

-- BOOK: begin measure-subadditive
-- 劣加法性: 交わっていてもよい。被覆から上からの評価が得られる
example (α : Type) [MeasurableSpace α] (μ : Measure α)
    (s : ℕ → Set α) : μ (⋃ i, s i) ≤ ∑' i, μ (s i) :=
  measure_iUnion_le s

-- 測度ゼロの集合を可算個集めても測度ゼロのまま
example (α : Type) [MeasurableSpace α] (μ : Measure α)
    (s : ℕ → Set α) (h : ∀ i, μ (s i) = 0) : μ (⋃ i, s i) = 0 :=
  measure_iUnion_null h
-- BOOK: end measure-subadditive

-- BOOK: begin volume-interval
-- 区間のルベーグ測度は長さ。ℝ の「長さ」の厳密な定義
example (a b : ℝ) : volume (Set.Icc a b) = ENNReal.ofReal (b - a) :=
  Real.volume_Icc

-- 開区間でも同じ。端点の2点は測度に寄与しない
example (a b : ℝ) : volume (Set.Ioo a b) = ENNReal.ofReal (b - a) :=
  Real.volume_Ioo
-- BOOK: end volume-interval

end Handbook.C33
