/- English edition source: Handbook/C29_Groups/S03_Quotient.lean. -/
import Mathlib

namespace Handbook.C29

-- BOOK: begin normal-def
-- A normal subgroup: closed under conjugation, the condition for
-- forming a quotient group
#check @Subgroup.Normal

-- In an abelian group every subgroup is normal (conjugation does
-- nothing)
example (G : Type) [CommGroup G] (H : Subgroup G) : H.Normal :=
  Subgroup.normal_of_isMulCommutative H
-- BOOK: end normal-def

-- BOOK: begin normal-center
-- The center is always a normal subgroup; by definition conjugation
-- has no effect on it
example (G : Type) [Group G] : (Subgroup.center G).Normal :=
  inferInstance

-- A kernel is always normal: what a homomorphism collapses is not
-- moved by conjugation
example (G H : Type) [Group G] [Group H] (f : G →* H) :
    f.ker.Normal :=
  inferInstance
-- BOOK: end normal-center

-- BOOK: begin quotient-mk
-- The canonical projection to the quotient group has kernel exactly N.
example (G : Type) [Group G] (N : Subgroup G) [N.Normal] :
    (QuotientGroup.mk' N).ker = N :=
  QuotientGroup.ker_mk' N
-- BOOK: end quotient-mk

-- BOOK: begin index-card
-- |G| = |H| × [G:H]: Lagrange's theorem as an equation
example (G : Type) [Group G] (H : Subgroup G) :
    Nat.card H * H.index = Nat.card G :=
  Subgroup.card_mul_index H
-- BOOK: end index-card

end Handbook.C29
