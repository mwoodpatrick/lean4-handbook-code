/- English edition source: Handbook/C16_Sets/S04_Quotient.lean. -/
import Mathlib

namespace Handbook.C16

-- BOOK: begin setoid-def
-- Equivalence relation: regard natural numbers of the same parity as
-- “the same”
def parity : Setoid ℕ :=
  ⟨fun a b => a % 2 = b % 2,
   ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩

-- The quotient type Quotient parity is “a world that sees only parity”
#check Quotient parity
-- BOOK: end setoid-def

-- BOOK: begin quotient-mk
-- In the quotient world, 3 and 5 become the same element
example : Quotient.mk parity 3 = Quotient.mk parity 5 :=
  Quotient.sound rfl
-- BOOK: end quotient-mk

-- BOOK: begin quotient-lift
-- Define a function on a quotient by proving it does not depend on the
-- representative
-- Here we extract “parity → 0/1” from the quotient
def parityBit : Quotient parity → ℕ :=
  Quotient.lift (fun n => n % 2) (fun _ _ h => h)

example : parityBit (Quotient.mk parity 7) = 1 := rfl
-- BOOK: end quotient-lift

-- BOOK: begin quotient-square
-- The same mechanism on ℤ modulo 3: n ↦ [n²] descends to the quotient
-- because n ≡ m (mod 3) forces n² ≡ m² (mod 3)
def mod3 : Setoid ℤ :=
  ⟨fun a b => a % 3 = b % 3,
   ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩

def sqMod3 : Quotient mod3 → ℤ :=
  Quotient.lift (fun n => n ^ 2 % 3) (fun _ _ h => Int.ModEq.pow 2 h)

-- 4 ≡ 1 (mod 3), and both squares leave the remainder 1
example : sqMod3 (Quotient.mk mod3 4) = 1 := by decide
-- BOOK: end quotient-square

end Handbook.C16
