/- Chapter 22: Linear algebra I
   22.5 Linear independence and the existence of a basis -/
import Mathlib

namespace Handbook.C22

-- BOOK: begin span-singleton
-- The subspace spanned by one vector is the set of its multiples
example (K V : Type) [Field K] [AddCommGroup V] [Module K V]
    (v w : V) :
    w ∈ Submodule.span K {v} ↔ ∃ c : K, c • v = w :=
  Submodule.mem_span_singleton
-- BOOK: end span-singleton

-- BOOK: begin indep-def
-- Linear independence: only the trivial combination gives zero
#check @LinearIndependent
-- a basis is linearly independent (part of the definition)
#check @Module.Basis.linearIndependent
-- BOOK: end indep-def

-- BOOK: begin basis-repr
-- A basis fixes coordinates; repr is the isomorphism reading
-- off the coefficients
#check @Module.Basis.repr
-- the dimension equals the cardinality of a basis
#check @Module.finrank_eq_card_basis
-- BOOK: end basis-repr

-- BOOK: begin basis-exists
-- Every vector space has a basis (using the axiom of choice,
-- Chapter 28)
example (K V : Type) [Field K] [AddCommGroup V] [Module K V] :
    ∃ s : Set V, Nonempty (Module.Basis s K V) :=
  Module.Basis.exists_basis K V
-- BOOK: end basis-exists

end Handbook.C22
