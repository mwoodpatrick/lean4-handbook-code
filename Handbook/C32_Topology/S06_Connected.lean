/- 第32章 位相空間論
   32.6 連結性 -/
import Mathlib

namespace Handbook.C32

-- BOOK: begin connected-image
-- 連結集合の連続像は連結(中間値の定理の位相的な本体)
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (s : Set X) (hs : IsConnected s)
    (hf : ContinuousOn f s) : IsConnected (f '' s) :=
  hs.image f hf
-- BOOK: end connected-image

-- BOOK: begin connected-icc
-- 区間は連結。これと上の補題だけで中間値の定理が出る
example (a b : ℝ) : IsPreconnected (Set.Icc a b) :=
  isPreconnected_Icc
-- BOOK: end connected-icc

-- BOOK: begin ivt
-- 中間値の定理: f a と f b の間の値はすべて像に現れる
example (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) :
    Set.Icc (f a) (f b) ⊆ f '' Set.Icc a b :=
  intermediate_value_Icc hab hf

-- 具体例: x³ + x - 1 は 0 と 1 の間に零点を持つ
example : ∃ x ∈ Set.Icc (0 : ℝ) 1, x ^ 3 + x - 1 = 0 := by
  have hc : ContinuousOn (fun x : ℝ => x ^ 3 + x - 1)
      (Set.Icc 0 1) := by fun_prop
  have h := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hc
  have h0 : (0 : ℝ) ∈ Set.Icc ((0:ℝ) ^ 3 + 0 - 1)
      ((1:ℝ) ^ 3 + 1 - 1) := by norm_num
  obtain ⟨x, hx, hfx⟩ := h h0
  exact ⟨x, hx, hfx⟩
-- BOOK: end ivt

-- BOOK: begin connected-component
-- 連結成分: 点 x を含む最大の連結集合。空間を塊に分割する
example (X : Type) [TopologicalSpace X] (x : X) :
    IsConnected (connectedComponent x) :=
  isConnected_connectedComponent

-- 弧状連結ならば連結(逆は一般には成り立たない)
example (X : Type) [TopologicalSpace X] (s : Set X)
    (hs : IsPathConnected s) : IsConnected s :=
  hs.isConnected
-- BOOK: end connected-component

end Handbook.C32
