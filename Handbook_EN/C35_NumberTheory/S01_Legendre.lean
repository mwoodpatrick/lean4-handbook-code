/- English edition source: Handbook/C35_NumberTheory/S01_Legendre.lean. -/
import Mathlib

namespace Handbook.C35

-- p = 7 numeric instances to fix and define concrete values
instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

-- BOOK: begin legendre-values
-- The Legendre symbol: 1 for a quadratic residue, −1 for a
-- non-residue, and 0 for a multiple of p
example : legendreSym 7 2 = 1 := by decide
example : legendreSym 7 3 = -1 := by decide
example : legendreSym 7 7 = 0 := by decide

-- 2 is a quadratic residue mod 7: 3² = 9 ≡ 2
example : (3 : ZMod 7) ^ 2 = 2 := by decide
-- BOOK: end legendre-values

-- BOOK: begin euler-criterion
-- Euler's criterion: a is a residue ⟺ a^((p−1)/2) = 1
example (p : ℕ) [Fact p.Prime] (a : ZMod p) (ha : a ≠ 0) :
    IsSquare a ↔ a ^ (p / 2) = 1 :=
  ZMod.euler_criterion p ha
-- BOOK: end euler-criterion

-- BOOK: begin quad-reciprocity
-- Quadratic reciprocity, relating the residues of two odd primes
example (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym q p * legendreSym p q = (-1) ^ (p / 2 * (q / 2)) :=
  legendreSym.quadratic_reciprocity hp hq hpq

-- The first supplement: whether −1 is a residue depends on p mod 4
example (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p (-1) = ZMod.χ₄ p :=
  legendreSym.at_neg_one hp
-- BOOK: end quad-reciprocity

end Handbook.C35
