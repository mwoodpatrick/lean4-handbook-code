/- Chapter 31: Field theory and Galois theory
   31.3 Towers, adjunction, splitting fields, finite fields -/
import Mathlib

namespace Handbook.C31

-- BOOK: begin tower-law
-- The tower law: stacking extensions multiplies the degrees
example (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] [Module.Finite K L] [Module.Finite L M] :
    Module.finrank K L * Module.finrank L M
      = Module.finrank K M :=
  Module.finrank_mul_finrank K L M
-- BOOK: end tower-law

-- BOOK: begin adjoin
-- Adjunction: the smallest intermediate field obtained by adding α to K
#check @IntermediateField.adjoin
-- an extension of degree 1 is the base field itself
#check @IntermediateField.finrank_bot
-- BOOK: end adjoin

-- BOOK: begin splitting
-- A splitting field: the smallest extension in which the polynomial
-- factors into linear factors
#check @Polynomial.IsSplittingField
-- an algebraic closure: an extension splitting every polynomial.
-- It always exists (by Zorn)
#check @AlgebraicClosure
-- BOOK: end splitting

-- BOOK: begin finite-field
-- The order of a finite field is always a prime power
example (K : Type) [Field K] [Fintype K] :
    ∃ p, CharP K p ∧ ∃ n : ℕ+, Nat.Prime p ∧
      Fintype.card K = p ^ (n : ℕ) :=
  FiniteField.card' K
-- BOOK: end finite-field

end Handbook.C31
