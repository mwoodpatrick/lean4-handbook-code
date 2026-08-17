/- 第12章 数列と数学的帰納法
   12.7 帰納法の練習曲 -/
import Mathlib

namespace Handbook.C12

-- BOOK: begin etude-pow
-- n < 2^n。帰納段では 2^n ≥ 1 という一言を omega に添える。
theorem lt_two_pow (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [pow_succ]
    omega
-- BOOK: end etude-pow

-- BOOK: begin etude-factorial
-- 2^n ≤ (n+1)!。階乗の増加は指数より速い。
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
-- ベルヌーイの不等式 (1+x)^n ≥ 1 + nx(x ≥ -1)。
-- 帰納段の掛け算で符号条件 1 + x ≥ 0 が効く。
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
-- どちらも mathlib に一般形がある
#check @Nat.lt_two_pow_self -- n < 2 ^ n
#check @one_add_mul_le_pow  -- ベルヌーイの不等式(一般の環)
-- BOOK: end etude-mathlib

end Handbook.C12
