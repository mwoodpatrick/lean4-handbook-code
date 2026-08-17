/- 第28章 数学基礎論と公理的集合論
   28.5 選択公理とその同値命題 -/
import Mathlib

namespace Handbook.C28

-- BOOK: begin choice-zorn
-- Zorn の補題: 任意の鎖が上界を持つなら極大元がある。
-- 選択公理と同値で、存在証明の主力になる
#check @zorn_le
-- BOOK: end choice-zorn

-- BOOK: begin choice-basis
-- 選択公理の代表的な帰結: どんなベクトル空間にも基底がある
example (K V : Type) [Field K] [AddCommGroup V] [Module K V] :
    ∃ s : Set V, Nonempty (Module.Basis s K V) :=
  Module.Basis.exists_basis K V
-- BOOK: end choice-basis

-- BOOK: begin choice-audit
-- #print axioms でどの公理に依存したかを機械的に監査できる。
-- Classical.choice が出れば選択公理を使っている
#print axioms Module.Basis.exists_basis
#print axioms Cardinal.cantor

-- 出力(両方とも):
-- depends on axioms: [propext, Classical.choice, Quot.sound]
-- BOOK: end choice-audit

end Handbook.C28
