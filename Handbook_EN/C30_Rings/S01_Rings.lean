/- English edition source: Handbook/C30_Rings/S01_Rings.lean. -/
import Mathlib

namespace Handbook.C30

-- BOOK: begin ring-ideal
-- An ideal: closed under addition, and multiplying by any ring
-- element keeps you inside
example (R : Type) [CommRing R] (I : Ideal R) (r x : R)
    (hx : x ∈ I) : r * x ∈ I :=
  I.mul_mem_left r hx

-- the quotient ring is the quotient by an ideal
#check @Ideal.Quotient.mk
-- BOOK: end ring-ideal

-- BOOK: begin ring-hom
-- A ring homomorphism R →+* S preserves both addition and
-- multiplication
example (R S : Type) [CommRing R] [CommRing S] (f : R →+* S)
    (a b : R) : f (a * b) = f a * f b :=
  f.map_mul a b

-- First isomorphism theorem: R/ker f ≅ im f (same design as in group
-- theory)
noncomputable example (R S : Type) [CommRing R] [CommRing S]
    (f : R →+* S) : (R ⧸ RingHom.ker f) ≃+* f.range :=
  RingHom.quotientKerEquivRange f
-- BOOK: end ring-hom

-- BOOK: begin polynomial
open Polynomial in
-- The polynomial ring ℚ[X]; X is the indeterminate
example : (X + 1 : Polynomial ℚ) * (X - 1) = X ^ 2 - 1 := by
  ring
-- BOOK: end polynomial

-- BOOK: begin ufd
-- ℤ is a principal ideal domain (PID) and a unique factorization
-- domain (UFD)
example : IsPrincipalIdealRing ℤ := inferInstance
example : UniqueFactorizationMonoid ℤ := inferInstance
-- BOOK: end ufd

-- BOOK: begin prime-maximal
-- A prime ideal: ab ∈ 𝔭 implies a ∈ 𝔭 or b ∈ 𝔭
-- (the generalization of a prime number)
example (R : Type) [CommRing R] (P : Ideal R) :
    P.IsPrime ↔ P ≠ ⊤ ∧ ∀ {x y : R}, x * y ∈ P → x ∈ P ∨ y ∈ P :=
  Ideal.isPrime_iff

-- maximal ⟺ the quotient is a field
example (R : Type) [CommRing R] (I : Ideal R) :
    I.IsMaximal ↔ IsField (R ⧸ I) :=
  Ideal.Quotient.maximal_ideal_iff_isField_quotient I
-- BOOK: end prime-maximal

-- BOOK: begin crt
-- The Chinese remainder theorem for ZMod: for coprime moduli the
-- quotient ring splits as a direct product
example (m n : ℕ) (h : m.Coprime n) :
    ZMod (m * n) ≃+* ZMod m × ZMod n :=
  ZMod.chineseRemainder h
-- BOOK: end crt

end Handbook.C30
