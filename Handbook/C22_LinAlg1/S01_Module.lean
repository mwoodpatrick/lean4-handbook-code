/- 第22章 線形代数I — ベクトル空間と線形写像
   22.1 ベクトル空間の公理 / 22.2 部分空間 -/
import Mathlib

namespace Handbook.C22

variable (V : Type) [AddCommGroup V] [Module ℝ V]

-- BOOK: begin module-axioms
-- ベクトル空間の公理は Module 型クラスの定理として使える
example (a : ℝ) (v w : V) : a • (v + w) = a • v + a • w :=
  smul_add a v w

example (v : V) : (0 : ℝ) • v = 0 := zero_smul ℝ v
-- BOOK: end module-axioms

-- BOOK: begin submodule
-- 部分空間 Submodule: 和とスカラー倍で閉じた部分集合
example (W : Submodule ℝ V) (v w : V)
    (hv : v ∈ W) (hw : w ∈ W) : v + w ∈ W :=
  W.add_mem hv hw

example (W : Submodule ℝ V) (a : ℝ) (v : V) (hv : v ∈ W) :
    a • v ∈ W :=
  W.smul_mem a hv
-- BOOK: end submodule

-- BOOK: begin span-mem
-- 生成元は必ずその生成部分空間に属する
example (S : Set V) (v : V) (hv : v ∈ S) :
    v ∈ Submodule.span ℝ S :=
  Submodule.subset_span hv

-- span S ≤ W を示すのは「S の各元が W に入る」だけでよい(最小性)
example (S : Set V) (W : Submodule ℝ V) (h : S ⊆ W) :
    Submodule.span ℝ S ≤ W :=
  Submodule.span_le.mpr h
-- BOOK: end span-mem

end Handbook.C22
