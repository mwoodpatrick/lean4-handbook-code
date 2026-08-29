/- Chapter 2: A tour of Lean 4 -/
import Mathlib

namespace Handbook.C02

-- BOOK: begin tour-one-one
-- 1 + 1 = 2. The whole panorama of mathematics starts here.
example : 1 + 1 = 2 := by norm_num
-- A proof may be checkable by computation, or it may follow
-- immediately from the definitions (rfl).
example : 1 + 1 = 2 := rfl
-- BOOK: end tour-one-one

-- BOOK: begin tour-false
-- A false claim cannot be proved. "Not equal" is a theorem too.
example : 1 + 1 ≠ 3 := by decide
-- BOOK: end tour-false

-- BOOK: begin tour-compute
-- Lean is a proof assistant and a calculator at the same time.
#eval 2 ^ 100
-- output: 1267650600228229401496703205376
-- BOOK: end tour-compute

-- BOOK: begin tour-compute2
-- Fractions are exact and whole lists can be computed
#eval (1 / 3 + 1 / 6 : ℚ)              -- output: 1/2
#eval (List.range 10).map (2 ^ ·)      -- the powers of 2
#eval Nat.minFac 91                    -- output: 7 (least prime factor)
-- BOOK: end tour-compute2

-- BOOK: begin tour-bignum
-- Arbitrary precision is a tool for counterexamples. The number
-- 2⁶⁷ − 1, which Mersenne claimed to be prime, is composite
-- (Cole, 1903).
#eval 2 ^ 67 - 1   -- output: 147573952589676412927

example : 2 ^ 67 - 1 = 193707721 * 761838257287 := by
  norm_num
-- BOOK: end tour-bignum

-- BOOK: begin tour-sqrt2
-- "The square root of 2 is irrational": the great theorem of
-- ancient Greece is quoted in one line.
example : Irrational (Real.sqrt 2) := irrational_sqrt_two
-- BOOK: end tour-sqrt2

-- BOOK: begin tour-sqrt-gen
-- The generalization is one line too: the square root of any prime
-- is irrational.
example : Irrational (Real.sqrt 3) :=
  Nat.prime_three.irrational_sqrt
-- BOOK: end tour-sqrt-gen

-- BOOK: begin tour-sqrt2-approx
-- Squeezing by approximations is a theorem: 1.414² < 2 < 1.415²
example : (1.414 : ℚ) ^ 2 < 2 ∧ 2 < (1.415 : ℚ) ^ 2 := by
  constructor <;> norm_num
-- BOOK: end tour-sqrt2-approx

-- BOOK: begin tour-primes
-- "There are infinitely many primes": Euclid's theorem.
-- For every n there is a prime p at least n.
example (n : ℕ) : ∃ p, n ≤ p ∧ p.Prime :=
  Nat.exists_infinite_primes n
-- BOOK: end tour-primes

-- BOOK: begin tour-primes-count
-- There are exactly 25 primes below 100
-- (both the counting and the proof are the machine's work)
#eval ((Finset.range 100).filter Nat.Prime).card      -- output: 25

example : ((Finset.range 100).filter Nat.Prime).card = 25 := by
  decide
-- BOOK: end tour-primes-count

-- BOOK: begin tour-deriv
-- Derivatives are computed as theorems too.
-- The derivative of x² at x = 3 is 6.
example : deriv (fun x : ℝ => x ^ 2) 3 = 6 := by
  norm_num [deriv_pow]
-- the derivative of sin is cos; a theorem of analysis in one line
example : deriv Real.sin = Real.cos := Real.deriv_sin
-- the slope of the exponential at 0 is 1 (the heart of e)
example : deriv Real.exp 0 = 1 := by
  simp [Real.deriv_exp]
-- BOOK: end tour-deriv

-- BOOK: begin tour-imo
-- IMO 1959 problem 1: (21n+4)/(14n+3) is in lowest terms for every n
theorem imo1959_p1 (n : ℕ) :
    Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
  have h := Nat.dvd_sub
    ((Nat.gcd_dvd_right (21 * n + 4) (14 * n + 3)).mul_left 3)
    ((Nat.gcd_dvd_left (21 * n + 4) (14 * n + 3)).mul_left 2)
  have e : 3 * (14 * n + 3) - 2 * (21 * n + 4) = 1 := by omega
  rw [e] at h
  exact Nat.dvd_one.mp h
-- BOOK: end tour-imo

-- BOOK: begin tour-decide
-- A finite claim is settled by decide, which checks every case.
-- 97 is prime; 91 is not (91 = 7 × 13).
example : Nat.Prime 97 := by decide
example : ¬ Nat.Prime 91 := by decide
-- BOOK: end tour-decide

-- BOOK: begin tour-deriv-min
-- A foretaste of what derivatives are for:
-- the minimum of x² − 6x + 13 is 4, attained at x = 3
example (x : ℝ) : 4 ≤ x ^ 2 - 6 * x + 13 := by
  nlinarith [sq_nonneg (x - 3)]
example : (3 : ℝ) ^ 2 - 6 * 3 + 13 = 4 := by norm_num
-- BOOK: end tour-deriv-min

-- BOOK: begin tour-limit
-- Limits are theorems: 1/n → 0 (Chapter 17)
example :
    Filter.Tendsto (fun n : ℕ => (1 : ℝ) / n)
      Filter.atTop (nhds 0) :=
  tendsto_one_div_atTop_nhds_zero_nat
-- and so are infinite series: 1 + 1/2 + 1/4 + … = 2 (Chapter 21)
example : ∑' n : ℕ, (1 / 2 : ℝ) ^ n = 2 := tsum_geometric_two
-- BOOK: end tour-limit

-- BOOK: begin tour-algebra
-- Expanding and factoring are left entirely to ring (Chapter 6)
example (x y : ℚ) : (x + y) * (x - y) = x ^ 2 - y ^ 2 := by
  ring
-- on a twelve-hour clock, 7 + 8 = 3 (congruences, Chapter 14)
example : (7 : ZMod 12) + 8 = 3 := by decide
-- BOOK: end tour-algebra

-- BOOK: begin tour-dice
-- The probability that two dice sum to 7 is 6/36 = 1/6 (Chapter 13)
-- (faces are held as 0..5, so the sum 7 is internally the sum 5)
#eval ((Finset.range 6) ×ˢ (Finset.range 6)).card   -- output: 36
#eval (((Finset.range 6) ×ˢ (Finset.range 6)).filter
       (fun p => p.1 + p.2 = 5)).card               -- output: 6
-- BOOK: end tour-dice

-- BOOK: begin tour-det
-- A determinant is one line too (linear algebra, Chapter 23)
example : (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℤ).det = -2 := by
  rw [Matrix.det_fin_two_of]
  norm_num
-- BOOK: end tour-det

-- BOOK: begin tour-exercises
-- Exercises: three claims checkable with this chapter's tools alone
example : 2 ^ 10 = 1024 := by norm_num
example : Nat.gcd 111 74 = 37 := by decide
example : (5 : ZMod 12) + 9 = 2 := by decide
-- BOOK: end tour-exercises

-- BOOK: begin tour-error
/- Submitting a wrong proof:

    example : 1 + 1 = 3 := rfl

  Lean's reply (the error message):

    type mismatch
      rfl
    has type
      ?a = ?a : Prop
    but is expected to have type
      1 + 1 = 3 : Prop

  "The type of rfl (an equation with the same shape on both sides)
   does not match the requested type 1 + 1 = 3."  -/
-- BOOK: end tour-error

-- BOOK: begin tour-error2
/- Frequent error number two, a mistyped name:

    example (a b : ℕ) : a.gcd b ∣ a := Nat.gcd_dvd_lef a b

  Lean's reply:

    unknown constant 'Nat.gcd_dvd_lef'

  "No declaration by that name exists."
  The correct name is Nat.gcd_dvd_left (the final t was missing). -/
-- BOOK: end tour-error2

end Handbook.C02
