/- English edition source: Handbook/C30_Rings/S03_Poly.lean. -/
import Mathlib

namespace Handbook.C30

open Polynomial

-- BOOK: begin poly-degree
-- The degree lives in WithBot ℕ, so the zero polynomial can be
-- given degree ⊥
#check @Polynomial.degree

-- the degree of a product is the sum of the degrees
example (R : Type) [CommRing R] [IsDomain R] (p q : R[X]) :
    (p * q).degree = p.degree + q.degree :=
  degree_mul
-- BOOK: end poly-degree

-- BOOK: begin poly-factor
-- a is a root exactly when X − a divides the polynomial
example (R : Type) [CommRing R] (p : R[X]) (a : R) :
    (X - C a) ∣ p ↔ p.IsRoot a :=
  dvd_iff_isRoot
-- BOOK: end poly-factor

-- BOOK: begin poly-euclid
-- The polynomial ring over a field is a Euclidean domain,
-- so division with remainder is available
noncomputable example (K : Type) [Field K] :
    EuclideanDomain K[X] :=
  inferInstance

-- it is a principal ideal domain too
example (K : Type) [Field K] : IsPrincipalIdealRing K[X] :=
  inferInstance
-- BOOK: end poly-euclid

-- BOOK: begin poly-noetherian
-- Hilbert's basis theorem: the polynomial ring over a Noetherian
-- ring is Noetherian
#check @Polynomial.isNoetherianRing
-- BOOK: end poly-noetherian

end Handbook.C30
