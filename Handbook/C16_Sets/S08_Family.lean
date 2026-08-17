/- 第16章 集合と写像
   16.3 集合族の和と共通部分 -/
import Mathlib

namespace Handbook.C16

-- BOOK: begin family-def
-- 添字づけられた和集合。⋃ i, A i と書く
example (A : ℕ → Set ℕ) (x : ℕ) :
    x ∈ ⋃ i, A i ↔ ∃ i, x ∈ A i := Set.mem_iUnion

-- どの A i も和集合に含まれる
example (A : ℕ → Set ℕ) (i : ℕ) : A i ⊆ ⋃ j, A j :=
  Set.subset_iUnion A i
-- BOOK: end family-def

-- BOOK: begin family-demorgan
-- de Morgan の法則の集合族版。無限個でも成り立つ
example (A : ℕ → Set ℕ) : (⋃ i, A i)ᶜ = ⋂ i, (A i)ᶜ :=
  Set.compl_iUnion A

-- 共通部分は各成分に含まれる(和集合と向きが逆)
#check @Set.iInter_subset
-- BOOK: end family-demorgan

-- BOOK: begin family-distrib
-- 分配法則。和集合と交わりの順序を入れ替えられる
#check @Set.iUnion_inter
-- BOOK: end family-distrib

end Handbook.C16
