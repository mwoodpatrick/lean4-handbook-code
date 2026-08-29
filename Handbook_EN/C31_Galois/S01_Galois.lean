/- Chapter 31: Field theory and Galois theory
   31.1 Fields and extensions / 31.9 Abel--Ruffini -/
import Mathlib

namespace Handbook.C31

-- BOOK: begin field-ext
-- The degree of a field extension: ℂ is 2-dimensional over ℝ
example : Module.finrank ℝ ℂ = 2 :=
  Complex.finrank_real_complex

-- an intermediate field (a field partway up an extension)
#check @IntermediateField
-- BOOK: end field-ext

-- BOOK: begin minpoly
-- The minimal polynomial: α is one of its roots, and it is irreducible
example (K L : Type) [Field K] [Field L] [Algebra K L] (α : L) :
    (Polynomial.aeval α) (minpoly K α) = 0 :=
  minpoly.aeval K α

example (K L : Type) [Field K] [Field L] [Algebra K L] (α : L)
    (h : IsIntegral K α) : Irreducible (minpoly K α) :=
  minpoly.irreducible h
-- BOOK: end minpoly

-- BOOK: begin galois
-- Galois extensions and the Galois correspondence
-- (the order-reversing correspondence between intermediate fields
-- and subgroups)
#check @IsGalois
#check @IsGalois.intermediateFieldEquivSubgroup
-- BOOK: end galois

-- BOOK: begin abel-ruffini
-- The core of Abel--Ruffini: for an element x expressible by radicals,
-- the Galois group of its minimal polynomial is solvable.
-- Contrapositively, "not solvable ⇒ not expressible by radicals".
example (F E : Type) [Field F] [Field E] [Algebra F E]
    (x : E) (hx : x ∈ solvableByRad F E) :
    IsSolvable (minpoly F x).Gal :=
  isSolvable_gal_minpoly hx
-- BOOK: end abel-ruffini

end Handbook.C31
