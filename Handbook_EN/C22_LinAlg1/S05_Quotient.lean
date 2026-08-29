/- Chapter 22: Linear algebra I
   22.7 Quotient spaces, dimension formulas, duality -/
import Mathlib

namespace Handbook.C22

-- BOOK: begin quotient-space
-- The quotient V/W. Dividing by a subspace needs no extra condition:
-- addition is commutative, so every subspace is "normal"
#check @Submodule.Quotient.mk
-- first isomorphism theorem: V/ker f ≅ im f (as for groups and rings)
#check @LinearMap.quotKerEquivRange
-- BOOK: end quotient-space

-- BOOK: begin dimension-formula
-- Inclusion and exclusion for dimensions:
-- dim(U+W) + dim(U∩W) = dim U + dim W
#check @Submodule.finrank_sup_add_finrank_inf_eq
-- existence of a complement: some W always gives V = U ⊕ W
#check @IsCompl
-- BOOK: end dimension-formula

-- BOOK: begin dual-space
-- The dual space: all linear maps from V to the scalars.
-- It is a vector space too.
#check @Module.Dual
-- in finite dimensions the dimensions agree;
-- in infinite dimensions the dual is strictly larger
#check @Module.rank
-- BOOK: end dual-space

end Handbook.C22
