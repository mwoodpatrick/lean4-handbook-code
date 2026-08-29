/- English edition source: Handbook/C16_Sets/S08_Family.lean. -/
import Mathlib

namespace Handbook.C16

-- BOOK: begin family-def
-- An indexed union, written ⋃ i, A i
example (A : ℕ → Set ℕ) (x : ℕ) :
    x ∈ ⋃ i, A i ↔ ∃ i, x ∈ A i := Set.mem_iUnion

-- Every A i is contained in the union
example (A : ℕ → Set ℕ) (i : ℕ) : A i ⊆ ⋃ j, A j :=
  Set.subset_iUnion A i
-- BOOK: end family-def

-- BOOK: begin family-demorgan
-- The family-of-sets version of De Morgan’s law; it also holds for
-- infinite families
example (A : ℕ → Set ℕ) : (⋃ i, A i)ᶜ = ⋂ i, (A i)ᶜ :=
  Set.compl_iUnion A

-- The intersection is contained in each component (the direction is
-- opposite to unions)
#check @Set.iInter_subset
-- BOOK: end family-demorgan

-- BOOK: begin family-distrib
-- Distributivity: interchange the order of union and intersection
#check @Set.iUnion_inter
-- BOOK: end family-distrib

end Handbook.C16
