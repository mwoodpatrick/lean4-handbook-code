/- English edition source: Handbook/C12_Induction/S07_Etudes.lean. -/
import Mathlib

namespace Handbook.C12

-- BOOK: begin etude-pow
-- n < 2^n. In the induction step, give omega the additional fact 2^n ≥
-- 1.
theorem lt_two_pow (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [pow_succ]
    omega
-- BOOK: end etude-pow

-- BOOK: begin etude-factorial
-- 2^n ≤ (n+1)!. Factorial growth eventually outpaces exponential
-- growth.
open scoped Nat in
theorem two_pow_le_factorial (n : ℕ) : 2 ^ n ≤ (n + 1)! := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [pow_succ, Nat.factorial_succ]
    have h2 : 2 ≤ n + 2 := by omega
    calc 2 ^ n * 2 ≤ (n + 1)! * 2 := Nat.mul_le_mul_right 2 ih
      _ ≤ (n + 1)! * (n + 2) := Nat.mul_le_mul_left _ h2
      _ = (n + 2) * (n + 1)! := Nat.mul_comm _ _
-- BOOK: end etude-factorial

-- BOOK: begin etude-bernoulli
-- Bernoulli's inequality (1+x)^n ≥ 1 + nx (x ≥ -1).
-- The sign condition 1 + x ≥ 0 matters when multiplying in the
-- induction step.
theorem bernoulli (x : ℚ) (hx : -1 ≤ x) (n : ℕ) :
    1 + n * x ≤ (1 + x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h0 : (0 : ℚ) ≤ 1 + x := by linarith
    have h1 : (1 + ↑n * x) * (1 + x) ≤ (1 + x) ^ n * (1 + x) :=
      mul_le_mul_of_nonneg_right ih h0
    rw [pow_succ]
    push_cast
    nlinarith [sq_nonneg x, Nat.cast_nonneg (α := ℚ) n]
-- BOOK: end etude-bernoulli

-- BOOK: begin etude-mathlib
-- mathlib contains general forms of both results
#check @Nat.lt_two_pow_self -- n < 2 ^ n
-- Bernoulli's inequality (in a general ring)
#check @one_add_mul_le_pow
-- BOOK: end etude-mathlib

end Handbook.C12
