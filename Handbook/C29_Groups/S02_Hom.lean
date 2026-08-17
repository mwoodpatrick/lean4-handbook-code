/- 第29章 群論
   29.4 準同型 / 29.5 剰余群 / 29.7 Sylow -/
import Mathlib

namespace Handbook.C29

-- BOOK: begin hom
-- 群準同型 f : G →* H は積を保つ写像。単位元・逆元の保存は定理。
example (G H : Type) [Group G] [Group H] (f : G →* H) :
    f 1 = 1 :=
  f.map_one

example (G H : Type) [Group G] [Group H] (f : G →* H) (a : G) :
    f a⁻¹ = (f a)⁻¹ :=
  f.map_inv a
-- BOOK: end hom

-- BOOK: begin lagrange
-- ラグランジュの定理: 部分群の位数は群の位数を割る
example (G : Type) [Group G] [Fintype G] (H : Subgroup G) :
    Nat.card H ∣ Nat.card G :=
  Subgroup.card_subgroup_dvd_card H
-- BOOK: end lagrange

-- BOOK: begin orbit-stabilizer
-- 軌道・固定化群定理: |軌道| × |固定化群| = |群|
example (G X : Type) [Group G] [MulAction G X] [Fintype G]
    (x : X) [Fintype (MulAction.orbit G x)]
    [Fintype (MulAction.stabilizer G x)] :
    Fintype.card (MulAction.orbit G x) *
      Fintype.card (MulAction.stabilizer G x) = Fintype.card G :=
  MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := G) x
-- BOOK: end orbit-stabilizer

-- BOOK: begin sylow
-- Sylow の定理(存在): 位数 p^n が群の位数を割るなら
-- その大きさの部分群が存在する
example (G : Type) [Group G] [Finite G] (p n : ℕ) [Fact p.Prime]
    (hdvd : p ^ n ∣ Nat.card G) :
    ∃ H : Subgroup G, Nat.card H = p ^ n :=
  Sylow.exists_subgroup_card_pow_prime p hdvd
-- BOOK: end sylow

-- BOOK: begin first-iso
-- 第一同型定理: G/ker f ≅ im f
noncomputable example (G H : Type) [Group G] [Group H] (f : G →* H) :
    (G ⧸ f.ker) ≃* f.range :=
  QuotientGroup.quotientKerEquivRange f
-- BOOK: end first-iso

end Handbook.C29
