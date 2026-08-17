/- 第29章 群論
   29.1 群の公理と例 / 29.3 部分群 -/
import Mathlib

namespace Handbook.C29

-- BOOK: begin group-axioms
-- 群の計算は group タクティクが公理から自動で閉じる
example (G : Type) [Group G] (a b : G) :
    a * b * b⁻¹ = a := by group

example (G : Type) [Group G] (a b : G) :
    (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  mul_inv_rev a b
-- BOOK: end group-axioms

-- BOOK: begin subgroup
-- 部分群: 積と逆元で閉じた部分集合
example (G : Type) [Group G] (H : Subgroup G) (a b : G)
    (ha : a ∈ H) (hb : b ∈ H) : a * b ∈ H :=
  H.mul_mem ha hb

example (G : Type) [Group G] (H : Subgroup G) (a : G)
    (ha : a ∈ H) : a⁻¹ ∈ H :=
  H.inv_mem ha
-- BOOK: end subgroup

-- BOOK: begin subgroup-closure
-- 生成 closure S は「S を含む最小の部分群」
-- 生成元は必ず closure に属する
example (G : Type) [Group G] (S : Set G) : S ⊆ Subgroup.closure S :=
  Subgroup.subset_closure

-- closure S ≤ H を示すのは「S ⊆ H」だけでよい(最小性)
example (G : Type) [Group G] (S : Set G) (H : Subgroup G)
    (h : S ⊆ H) : Subgroup.closure S ≤ H :=
  (Subgroup.closure_le H).mpr h
-- BOOK: end subgroup-closure

-- BOOK: begin group-examples
-- 身近な群の例: 整数は加法群、ℤ/nℤ も加法群(第14章)
example : AddGroup ℤ := inferInstance

example (n : ℕ) [NeZero n] : AddCommGroup (ZMod n) := inferInstance
-- BOOK: end group-examples

end Handbook.C29
