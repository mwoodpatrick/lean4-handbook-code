/- Chapter 35: Number theory
   35.3 Fermat's two-square theorem -/
import Mathlib

namespace Handbook.C35

-- BOOK: begin two-squares
-- Fermat's two-square theorem (the Christmas theorem):
-- a prime p ≢ 3 (mod 4) is a sum of two squares
example (p : ℕ) [Fact p.Prime] (hp : p % 4 ≠ 3) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p :=
  Nat.Prime.sq_add_sq hp
-- BOOK: end two-squares

-- BOOK: begin two-squares-examples
-- Instances: a prime of the form 4k+1 can always be written so
example : 1 ^ 2 + 2 ^ 2 = 5 := by norm_num
example : 2 ^ 2 + 3 ^ 2 = 13 := by norm_num
example : 1 ^ 2 + 4 ^ 2 = 17 := by norm_num

-- 7, of the form 4k+3, cannot be:
-- a square is 0 or 1 mod 4
example : ∀ a b : ZMod 4, a ^ 2 + b ^ 2 ≠ 3 := by decide
-- BOOK: end two-squares-examples

-- BOOK: begin gaussian
-- In the Gaussian integers ℤ[i] the norm is multiplicative;
-- this is the background of sums of two squares
example (z w : GaussianInt) :
    (z * w).norm = z.norm * w.norm :=
  Zsqrtd.norm_mul z w

-- 5 factors as (2+i)(2-i): prime in ℤ but not in ℤ[i]
example : (⟨2, 1⟩ : GaussianInt) * ⟨2, -1⟩ = 5 := by decide
-- BOOK: end gaussian

end Handbook.C35
