/- English edition source: Handbook/C28_Foundations/S04_Type.lean. -/
import Mathlib

namespace Handbook.C28

-- BOOK: begin type-axioms
-- The only three axioms behind Lean.
-- propositional extensionality (equivalent propositions are equal)
#check @propext

-- soundness of quotients (equivalent elements have the same class)
#check @Quot.sound

-- the axiom of choice (extracting an element of a nonempty type)
#check @Classical.choice
-- BOOK: end type-axioms

-- BOOK: begin type-prop
-- Prop is the universe of propositions. By proof irrelevance,
-- two proofs of the same proposition are definitionally equal.
example (p : Prop) (h1 h2 : p) : h1 = h2 := rfl

-- Type is the universe of data; this does not hold there
#check @Nat
#check @Prop
-- BOOK: end type-prop

-- BOOK: begin type-noncomputable
-- A definition using the axiom above has no computation procedure,
-- so it is marked noncomputable
noncomputable def pick (α : Type) (h : Nonempty α) : α :=
  Classical.choice h

-- Dependent function type: the return type depends on the argument.
-- ZFC's functions cannot express this
#check @Vector
-- BOOK: end type-noncomputable

end Handbook.C28
