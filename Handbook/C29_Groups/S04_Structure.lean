/- 第29章 群論
   29.2 巡回群 / 29.8 対称群と単純群 -/
import Mathlib

namespace Handbook.C29

-- BOOK: begin cyclic-gen
-- 巡回群: 1つの元で生成される群
#check @IsCyclic

-- 生成元が存在する(定義の言い換え)
example (G : Type) [Group G] [IsCyclic G] :
    ∃ g : G, ∀ x : G, x ∈ Subgroup.zpowers g :=
  IsCyclic.exists_generator
-- BOOK: end cyclic-gen

-- BOOK: begin order-dvd
-- 元の位数は群の位数を割る。ラグランジュの定理の系である
example (G : Type) [Group G] [Fintype G] (g : G) :
    orderOf g ∣ Fintype.card G :=
  orderOf_dvd_card
-- BOOK: end order-dvd

-- BOOK: begin perm-sign
-- 対称群 Equiv.Perm α は α の置換全体のなす群
#check @Equiv.Perm

-- 符号は {±1} への準同型。偶置換・奇置換の区別を与える
#check @Equiv.Perm.sign

-- 交代群はその核。したがって常に正規部分群である
#check @alternatingGroup
-- BOOK: end perm-sign

-- BOOK: begin solvable
-- 可解群: 可換な層に分解できる群
#check @IsSolvable

-- 5次以上の対称群は可解でない。
-- これが5次方程式に解の公式がない理由である(第31章)
#check @Equiv.Perm.not_solvable
-- BOOK: end solvable

-- BOOK: begin abelian-structure
-- 有限アーベル群の構造定理: 素数冪位数の巡回群の直和に分解する
#check @AddCommGroup.equiv_directSum_zmod_of_finite
-- BOOK: end abelian-structure

end Handbook.C29
