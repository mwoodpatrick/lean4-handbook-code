/- 第29章 群論
   29.5 正規部分群と剰余群 -/
import Mathlib

namespace Handbook.C29

-- BOOK: begin normal-def
-- 正規部分群: 共役で閉じている。剰余群を作れる条件である
#check @Subgroup.Normal

-- 可換群ではすべての部分群が正規(共役が何もしないため)
example (G : Type) [CommGroup G] (H : Subgroup G) : H.Normal :=
  Subgroup.normal_of_isMulCommutative H
-- BOOK: end normal-def

-- BOOK: begin normal-center
-- 中心は常に正規部分群。定義から共役が自明に効かない
example (G : Type) [Group G] : (Subgroup.center G).Normal :=
  inferInstance

-- 核も常に正規。準同型で 1 に潰れる部分は共役で動かない
example (G H : Type) [Group G] [Group H] (f : G →* H) :
    f.ker.Normal :=
  inferInstance
-- BOOK: end normal-center

-- BOOK: begin quotient-mk
-- 剰余群への標準射影。核はちょうど N である
example (G : Type) [Group G] (N : Subgroup G) [N.Normal] :
    (QuotientGroup.mk' N).ker = N :=
  QuotientGroup.ker_mk' N
-- BOOK: end quotient-mk

-- BOOK: begin index-card
-- |G| = |H| × [G:H]。ラグランジュの定理の等式版
example (G : Type) [Group G] (H : Subgroup G) :
    Nat.card H * H.index = Nat.card G :=
  Subgroup.card_mul_index H
-- BOOK: end index-card

end Handbook.C29
