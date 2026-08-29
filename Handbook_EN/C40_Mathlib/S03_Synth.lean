/- Chapter 40: Finding your way around mathlib
   40.5 Swimming in the type class hierarchy -/
import Mathlib

namespace Handbook.C40

-- BOOK: begin synth
-- #synth answers how an instance was found
#synth Ring ℤ
#synth Field ℚ
-- BOOK: end synth

-- BOOK: begin synth-chain
-- The hierarchy climbs on its own:
-- a field is a ring is an additive group
example : Ring ℚ := inferInstance
example : AddCommGroup ℚ := inferInstance

-- ℕ is not a Ring: it has no subtraction
-- example : Ring ℕ := inferInstance   -- fails
example : CommSemiring ℕ := inferInstance
-- BOOK: end synth-chain

-- BOOK: begin synth-use
-- Stated with a type class hypothesis,
-- a lemma serves every fitting type
example {R : Type*} [CommRing R] (a b : R) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring

-- and ℤ is one special case of it
example (a b : ℤ) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring
-- BOOK: end synth-use

end Handbook.C40
