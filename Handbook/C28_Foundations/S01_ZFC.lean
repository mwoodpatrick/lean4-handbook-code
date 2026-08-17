/- 第28章 数学基礎論と公理的集合論
   28.2 ZFC / 28.3 順序数 / 28.5 選択公理 -/
import Mathlib

namespace Handbook.C28

-- BOOK: begin zfc
-- ZFC 集合論そのものが mathlib の1住人である
#check ZFSet     -- ZFC の集合の型
#check Ordinal   -- 順序数
#check Cardinal  -- 基数
-- BOOK: end zfc

-- BOOK: begin zfc-axioms
-- ZFSet では外延性が定理として成り立つ(同じ元をもつ集合は等しい)
example (x y : ZFSet) (h : ∀ z, z ∈ x ↔ z ∈ y) : x = y :=
  ZFSet.ext h

-- 空集合はどんな元も持たない
example (z : ZFSet) : z ∉ (∅ : ZFSet) := ZFSet.notMem_empty z
-- BOOK: end zfc-axioms

-- BOOK: begin transfinite
-- 超限帰納法: 「すべての小さい順序数で成立」から目標の順序数へ進む
-- (整礎な順序なら成り立つ一般形。順序数はその代表例)
example {p : Ordinal → Prop} (i : Ordinal)
    (h : ∀ j, (∀ k < j, p k) → p j) : p i :=
  WellFoundedLT.induction i h
-- BOOK: end transfinite

-- BOOK: begin cantor
-- カントールの定理(基数版): a < 2^a。冪集合は必ず真に大きい。
example (a : Cardinal) : a < 2 ^ a := Cardinal.cantor a

-- 無限基数の冪等性: κ + κ = κ、κ · κ = κ(ℵ₀ 以上)
example (κ : Cardinal) (h : Cardinal.aleph0 ≤ κ) : κ * κ = κ :=
  Cardinal.mul_eq_self h
-- BOOK: end cantor

-- BOOK: begin continuum
-- 実数の濃度は連続体 𝔠 = 2^ℵ₀。ℕ より真に大きい。
example : Cardinal.mk ℝ = 2 ^ Cardinal.aleph0 := by
  rw [Cardinal.mk_real, Cardinal.continuum]

-- したがって実数全体は可算でない(ℕ とは濃度が違う)
example : ¬ (Set.univ : Set ℝ).Countable :=
  Cardinal.not_countable_real
-- BOOK: end continuum

-- BOOK: begin diaconescu
-- Diaconescu の定理: 選択公理から排中律が導かれる。
-- mathlib の Classical.em はこの経路で証明されている。
#check @Classical.em

-- 排中律は「定理」として使える(mathlib は古典論理)
example (p : Prop) : p ∨ ¬ p := Classical.em p
-- BOOK: end diaconescu

end Handbook.C28
