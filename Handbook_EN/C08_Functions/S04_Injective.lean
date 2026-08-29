/- English edition source: Handbook/C08_Functions/S04_Injective.lean. -/
import Mathlib

namespace Handbook.C08

-- BOOK: begin inj-def
-- Injective: equal values force equal inputs
example : Function.Injective (fun x : ℚ => 2 * x + 1) := by
  intro a b h
  dsimp only at h
  linarith
-- BOOK: end inj-def

-- BOOK: begin surj-def
-- Surjective: every value has a preimage.
-- The witness is the formula of the inverse function itself.
example : Function.Surjective (fun x : ℚ => 2 * x + 1) := by
  intro y
  use (y - 1) / 2
  dsimp only
  ring
-- BOOK: end surj-def

-- BOOK: begin inj-counter
-- x² is not injective: 1 and -1 both go to the value 1
example : ¬ Function.Injective (fun x : ℤ => x ^ 2) := by
  intro h
  have : (1 : ℤ) = -1 := h (by norm_num)
  norm_num at this
-- BOOK: end inj-counter

-- BOOK: begin bij-def
-- Bijective = injective and surjective
example : Function.Bijective (fun x : ℚ => 2 * x + 1) :=
  ⟨fun a b h => by dsimp only at h; linarith,
   fun y => ⟨(y - 1) / 2, by dsimp only; ring⟩⟩
-- BOOK: end bij-def

-- BOOK: begin fun-count
-- Functions between finite sets can be counted: there are 2³ = 8
-- functions from a 3-element set to a 2-element set
example : (Finset.univ : Finset (Fin 3 → Fin 2)).card = 8 := by
  decide

-- there are 3 × 2 = 6 injections from a 2-element to a 3-element set
-- (the permutation ₃P₂)
example :
    ((Finset.univ : Finset (Fin 2 → Fin 3)).filter
      Function.Injective).card = 6 := by
  decide
-- BOOK: end fun-count

-- BOOK: begin equiv
-- Equiv (≃) is the data including the inverse:
-- the two functions and the two round-trip proofs
def double : ℚ ≃ ℚ where
  toFun x := 2 * x + 1
  invFun y := (y - 1) / 2
  left_inv x := by dsimp; ring
  right_inv y := by dsimp; ring

#eval double 3        -- Output: 7
#eval double.symm 7   -- Output: 3(Back)
-- BOOK: end equiv

end Handbook.C08
