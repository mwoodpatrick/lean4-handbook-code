/- English edition source: Handbook/C05_Proofs/S01_Prop.lean. -/
import Mathlib

namespace Handbook.C05

-- BOOK: begin prop-type
-- A proposition is a term of type Prop
#check 2 + 2 = 4       -- 2 + 2 = 4 : Prop
-- this is a perfectly good proposition too (though false)
#check 2 + 2 = 5
#check ∀ n : ℕ, 0 ≤ n  -- ∀ (n : ℕ), 0 ≤ n : Prop
-- BOOK: end prop-type

-- BOOK: begin prop-proof
-- To prove is to build a term whose type is the proposition
theorem two_add_two : 2 + 2 = 4 := rfl

#check two_add_two     -- two_add_two : 2 + 2 = 4
-- BOOK: end prop-proof

-- BOOK: begin prop-truefalse
-- The simplest propositions: True (proved by trivial) and False (which
-- has no proof)
example : True := trivial

-- Anything follows from False (the principle of explosion)
example (P : Prop) (h : False) : P := h.elim
-- BOOK: end prop-truefalse

end Handbook.C05
