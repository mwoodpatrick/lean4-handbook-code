/- Chapter 31: Field theory and Galois theory
   31.6 The Galois correspondence -/
import Mathlib

namespace Handbook.C31

-- BOOK: begin galois-card
-- In a Galois extension the number of automorphisms is exactly
-- the degree of the extension
example (F E : Type) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] :
    Nat.card (E ≃ₐ[F] E) = Module.finrank F E :=
  IsGalois.card_aut_eq_finrank F E
-- BOOK: end galois-card

-- BOOK: begin fixed-field
-- The elements fixed by a subgroup form an intermediate field
#check @IntermediateField.fixedField
-- the automorphisms fixing an intermediate field form a subgroup
#check @IntermediateField.fixingSubgroup
-- BOOK: end fixed-field

-- BOOK: begin galois-tfae
-- Equivalent characterizations of a Galois extension: the fixed field,
-- the number of automorphisms, being a splitting field --- conditions
-- of quite different appearance that coincide
#check @IsGalois.tfae
-- BOOK: end galois-tfae

end Handbook.C31
