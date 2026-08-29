/- English edition source: Handbook/C29_Groups/S02_Hom.lean. -/
import Mathlib

namespace Handbook.C29

-- BOOK: begin hom
-- f : G →* H is a map preserving the operation.
-- That it preserves the identity and inverses is a theorem.
example (G H : Type) [Group G] [Group H] (f : G →* H) :
    f 1 = 1 :=
  f.map_one

example (G H : Type) [Group G] [Group H] (f : G →* H) (a : G) :
    f a⁻¹ = (f a)⁻¹ :=
  f.map_inv a
-- BOOK: end hom

-- BOOK: begin lagrange
-- Lagrange's theorem: the order of a subgroup divides the order of
-- the group
example (G : Type) [Group G] [Fintype G] (H : Subgroup G) :
    Nat.card H ∣ Nat.card G :=
  Subgroup.card_subgroup_dvd_card H
-- BOOK: end lagrange

-- BOOK: begin orbit-stabilizer
-- Orbit--stabilizer: |orbit| × |stabilizer| = |group|
example (G X : Type) [Group G] [MulAction G X] [Fintype G]
    (x : X) [Fintype (MulAction.orbit G x)]
    [Fintype (MulAction.stabilizer G x)] :
    Fintype.card (MulAction.orbit G x) *
      Fintype.card (MulAction.stabilizer G x) = Fintype.card G :=
  MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := G) x
-- BOOK: end orbit-stabilizer

-- BOOK: begin sylow
-- Sylow's theorem (existence): if p^n divides the order of the group
-- there is a subgroup of that order
example (G : Type) [Group G] [Finite G] (p n : ℕ) [Fact p.Prime]
    (hdvd : p ^ n ∣ Nat.card G) :
    ∃ H : Subgroup G, Nat.card H = p ^ n :=
  Sylow.exists_subgroup_card_pow_prime p hdvd
-- BOOK: end sylow

-- BOOK: begin first-iso
-- The first isomorphism theorem: G/ker f ≃* im f
noncomputable example (G H : Type) [Group G] [Group H] (f : G →* H) :
    (G ⧸ f.ker) ≃* f.range :=
  QuotientGroup.quotientKerEquivRange f
-- BOOK: end first-iso

end Handbook.C29
