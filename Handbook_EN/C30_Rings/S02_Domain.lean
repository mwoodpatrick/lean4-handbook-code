/- Chapter 30: Ring theory
   30.3 Integral domains and factorization -/
import Mathlib

namespace Handbook.C30

-- BOOK: begin domain-zero-divisor
-- ℤ/6 is not a domain: 2·3 = 0 while 2 ≠ 0 and 3 ≠ 0
example : (2 : ZMod 6) * 3 = 0 := by decide
-- modulo a prime it becomes a field; the zero divisors disappear
example (p : ℕ) [Fact p.Prime] : Field (ZMod p) := inferInstance
-- BOOK: end domain-zero-divisor

-- BOOK: begin domain-cancel
-- A domain admits cancellation; this restates having no zero divisors
example (R : Type) [CommRing R] [IsDomain R] (a b c : R)
    (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
  mul_left_cancel₀ ha h
-- BOOK: end domain-cancel

-- BOOK: begin irreducible-prime
-- Irreducible (not factorable further) and prime (dividing a product
-- divides a factor)
#check @Irreducible
#check @Prime
-- in a unique factorization domain the two coincide.
-- In a general ring an irreducible element need not be prime
#check @UniqueFactorizationMonoid.irreducible_iff_prime
-- BOOK: end irreducible-prime

-- BOOK: begin maximal-exists
-- A ring with unit always has a maximal ideal (by Zorn's lemma)
#check @Ideal.exists_maximal
-- BOOK: end maximal-exists

end Handbook.C30
