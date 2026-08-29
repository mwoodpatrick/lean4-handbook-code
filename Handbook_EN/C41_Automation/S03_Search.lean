/- English edition source: Handbook/C41_Automation/S03_Search.lean. -/
import Mathlib

namespace Handbook.C41

-- BOOK: begin aesop
-- aesop: rule-based proof search, especially effective for routine
-- logic and set arguments.
example (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) (hp : P) :
    R ∧ P := by
  aesop

example (s t : Set ℕ) (x : ℕ) (h : x ∈ s) : x ∈ s ∪ t := by
  aesop
-- BOOK: end aesop

-- BOOK: begin aesop-limit
-- aesop is not universal: it is weak at arithmetic, which is left
-- to the dedicated tactics
example (a b : ℤ) (h : a ≤ b) : a - 1 < b := by
  omega

-- ring settles it for certain
example (x y : ℚ) : (x + y) ^ 2 - (x - y) ^ 2 = 4 * (x * y) := by
  ring
-- BOOK: end aesop-limit

end Handbook.C41
