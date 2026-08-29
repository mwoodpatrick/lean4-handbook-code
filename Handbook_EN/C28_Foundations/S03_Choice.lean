/- Chapter 28: Foundations and axiomatic set theory
   28.5 The axiom of choice -/
import Mathlib

namespace Handbook.C28

-- BOOK: begin choice-basis
-- The representative consequence of choice:
-- every vector space has a basis
example (K V : Type) [Field K] [AddCommGroup V] [Module K V] :
    ∃ s : Set V, Nonempty (Module.Basis s K V) :=
  Module.Basis.exists_basis K V
-- BOOK: end choice-basis

-- BOOK: begin choice-zorn
-- Zorn's lemma: if every chain has an upper bound there is a maximal
-- element. It is equivalent to choice and is the workhorse of
-- existence proofs.
#check @zorn_le
-- BOOK: end choice-zorn

-- BOOK: begin choice-audit
-- #print axioms audits mechanically which axioms were used.
-- Classical.choice appearing means the axiom of choice was used
#print axioms Module.Basis.exists_basis
#print axioms Cardinal.cantor
-- output (for both):
-- depends on axioms: [propext, Classical.choice, Quot.sound]
-- BOOK: end choice-audit

end Handbook.C28
