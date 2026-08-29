/- English edition source: Handbook/C14_Integers/S02_Gcd.lean. -/
import Mathlib

namespace Handbook.C14

-- BOOK: begin gcd-basic
#eval Nat.gcd 12 18  -- output: 6

-- One step of the Euclidean algorithm is available directly as a
-- theorem
example (a b : ℕ) : Nat.gcd a b = Nat.gcd (b % a) a :=
  Nat.gcd_rec a b

example (a b : ℕ) : Nat.gcd a b ∣ a := Nat.gcd_dvd_left a b
-- BOOK: end gcd-basic

-- BOOK: begin gcd-bezout
-- Bézout’s identity: the gcd is an integer linear combination of a and
-- b
example (a b : ℤ) :
    ∃ x y : ℤ, (Int.gcd a b : ℤ) = a * x + b * y :=
  ⟨Int.gcdA a b, Int.gcdB a b, Int.gcd_eq_gcd_ab a b⟩
-- BOOK: end gcd-bezout

-- BOOK: begin gcd-bezout-compute
-- Bézout coefficients are computed by running the Euclidean algorithm
-- backward (extended Euclid)
#eval Int.gcdA 3 5  -- output: 2
#eval Int.gcdB 3 5  -- output: -1

-- Check: 3·2 + 5·(−1) = 1 = gcd(3, 5)
example : (3 : ℤ) * 2 + 5 * (-1) = 1 := by norm_num
-- BOOK: end gcd-bezout-compute

-- BOOK: begin gcd-trace
-- Execution trace of Euclid’s algorithm: follow gcd(252, 105) by hand
#eval Nat.gcd 252 105  -- output: 21
-- 252 = 105·2 + 42 → 105 = 42·2 + 21 → 42 = 21·2 + 0
example : Nat.gcd 252 105 = 21 := by decide

-- The least common multiple is linked by product = gcd × lcm
example (a b : ℕ) : Nat.gcd a b * Nat.lcm a b = a * b :=
  Nat.gcd_mul_lcm a b
-- BOOK: end gcd-trace

-- BOOK: begin gcd-coprime
-- Coprime means gcd = 1; this also characterizes a fraction in lowest
-- terms.
example : Nat.Coprime 8 15 := by decide

-- If the factors are coprime, dividing their product implies dividing
-- one factor (Euclid’s lemma)
example (k m n : ℕ) (hk : Nat.Coprime k m) (h : k ∣ m * n) :
    k ∣ n :=
  hk.dvd_of_dvd_mul_left h
-- BOOK: end gcd-coprime

end Handbook.C14
