/- English edition source: Handbook/C04_Language/S08_Universes.lean. -/
import Mathlib

namespace Handbook.C04

-- BOOK: begin univ-tower
-- The type of types, its type, ... form an infinite tower (universes)
#check ℕ       -- ℕ : Type
#check Type    -- Type : Type 1
#check Type 1  -- Type 1 : Type 2
#check Prop    -- Prop : Type
-- BOOK: end univ-tower

-- BOOK: begin univ-dependent
-- Dependent type: the "type" of the return value depends on the "value"
-- of the argument
def Tuple (n : ℕ) : Type := Fin n → ℚ

def allZero (n : ℕ) : Tuple n := fun _ => 0

#check allZero 3  -- allZero 3 : Tuple 3
#check allZero 5  -- allZero 5 : Tuple 5 (the type has changed)
-- BOOK: end univ-dependent

-- BOOK: begin univ-poly
-- Universe polymorphism: a definition that works at any level carries a
-- universe variable u
universe u

def twice {α : Type u} (f : α → α) (a : α) : α := f (f a)

#eval twice (· + 10) 5         -- output: 25
#eval twice (List.cons 0) [1]  -- output: [0, 0, 1]
-- BOOK: end univ-poly

-- BOOK: begin univ-subtype
-- Subtype {x // P x}: bundles a value together with "a proof it
-- satisfies the condition"
def half : {q : ℚ // 0 < q} := ⟨1 / 2, by norm_num⟩

#eval half.val    -- output: 1/2 (the value part)
#check half.prop  -- the proof part, of 0 < 1/2
-- BOOK: end univ-subtype

-- BOOK: begin lang-exercises
-- Exercise: make one round trip of definition and verification with
-- this chapter's tools
def triple (n : ℕ) : ℕ := 3 * n

def isEven (n : ℕ) : Bool := n % 2 == 0

#eval triple 14  -- output: 42
#eval isEven 7   -- output: false

example : triple 4 = 12 := rfl
example (n : ℕ) : triple (n + 1) = triple n + 3 := by
  unfold triple
  ring
-- BOOK: end lang-exercises

end Handbook.C04
