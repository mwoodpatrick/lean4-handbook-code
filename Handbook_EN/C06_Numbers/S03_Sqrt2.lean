/- Chapter 6: Numbers and expressions
   6.4 Square roots -- the irrationality of √2 in full -/
import Mathlib

namespace Handbook.C06

-- BOOK: begin sqrt2-even
-- Lemma: if p² is even then so is p (because 2 is prime)
theorem two_dvd_of_two_dvd_sq {p : ℕ} (h : 2 ∣ p ^ 2) : 2 ∣ p :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
-- BOOK: end sqrt2-even

-- BOOK: begin sqrt2-core
-- The core: p² = 2q² is impossible for a fraction p/q in lowest terms
theorem sqrt2_core (p q : ℕ) (hcop : Nat.gcd p q = 1) :
    p ^ 2 ≠ 2 * q ^ 2 := by
  intro h
  -- p is even; write p = 2k
  have hp : 2 ∣ p := two_dvd_of_two_dvd_sq ⟨q ^ 2, h⟩
  obtain ⟨k, hk⟩ := hp
  -- BOOK: elide begin q is shown to be even in the same way
  rw [hk] at h
  have haux : (2 * k) ^ 2 = 4 * k ^ 2 := by ring
  have h4 : 4 * k ^ 2 = 2 * q ^ 2 := by linarith
  have hq2 : q ^ 2 = 2 * k ^ 2 := by linarith
  have hq : 2 ∣ q := two_dvd_of_two_dvd_sq ⟨k ^ 2, hq2⟩
  -- BOOK: elide end
  -- p and q both even makes the gcd at least 2,
  -- contradicting coprimality
  have : 2 ∣ Nat.gcd p q := Nat.dvd_gcd ⟨k, hk⟩ hq
  rw [hcop] at this
  omega
-- BOOK: end sqrt2-core

-- BOOK: begin sqrt2-mathlib
-- From mathlib's general theorem
-- (√n is irrational iff n is not a square)
example : Irrational (Real.sqrt 2) := irrational_sqrt_two
-- BOOK: end sqrt2-mathlib

-- BOOK: begin irrational-add
-- An irrational stays irrational after adding, or multiplying by
-- (a nonzero) rational
example (q : ℚ) : Irrational (Real.sqrt 2 + q) :=
  irrational_sqrt_two.add_ratCast q

example : Irrational (2 * Real.sqrt 2) := by
  have h := irrational_sqrt_two.ratCast_mul
    (show (2 : ℚ) ≠ 0 by norm_num)
  simpa using h
-- BOOK: end irrational-add

-- BOOK: begin sqrt2-rationalize
-- The heart of rationalizing: (√2 + 1)(√2 − 1) = 1,
-- so 1/(√2 − 1) = √2 + 1 (the root leaves the denominator)
example : (Real.sqrt 2 + 1) * (Real.sqrt 2 - 1) = 1 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  ring_nf
  linarith [h2]
-- BOOK: end sqrt2-rationalize

-- BOOK: begin sqrt2-dense
-- Density of the rationals: between any two reals there is a rational
example (x y : ℝ) (h : x < y) :
    ∃ q : ℚ, x < q ∧ (q : ℝ) < y :=
  exists_rat_btwn h
-- BOOK: end sqrt2-dense

end Handbook.C06
