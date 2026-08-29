/- English edition source: Handbook/C12_Induction/S06_Fibonacci.lean. -/
import Mathlib

namespace Handbook.C12

-- BOOK: begin fib-def
-- A recurrence referring two terms back.
-- The definition becomes Lean code as it stands.
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

#eval (List.range 8).map fib  -- Output: [0, 1, 1, 2, 3, 5, 8, 13]
-- BOOK: end fib-def

-- The gradation expression itself is from the definition rfl Contact Us
theorem fib_add_two (n : ℕ) :
    fib (n + 2) = fib n + fib (n + 1) := rfl

-- BOOK: begin fib-sum
-- The sum of the first n terms is fib (n+1) - 1, stated in the +1
-- form to avoid subtraction.
theorem fib_sum (n : ℕ) :
    (∑ i ∈ Finset.range n, fib i) + 1 = fib (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, add_right_comm, ih]
    have h : fib (n + 1 + 1) = fib n + fib (n + 1) := rfl
    omega
-- BOOK: end fib-sum

-- BOOK: begin fib-mathlib
-- It agrees with mathlib's Nat.fib (proved by functional induction)
theorem fib_eq_nat_fib (n : ℕ) : fib n = Nat.fib n := by
  induction n using fib.induct with
  | case1 => rfl
  | case2 => rfl
  | case3 n ih1 ih2 =>
    rw [fib_add_two, Nat.fib_add_two, ih1, ih2]
-- BOOK: end fib-mathlib

-- BOOK: begin fib-even
-- fib (3n) is even. Prepare the three-step recurrence and finish by
-- ordinary induction.
theorem fib_add_three (n : ℕ) :
    fib (n + 3) = 2 * fib (n + 1) + fib n := by
  have h : fib (n + 3) = fib (n + 1) + (fib n + fib (n + 1)) := rfl
  omega

theorem two_dvd_fib_three_mul (n : ℕ) : 2 ∣ fib (3 * n) := by
  induction n with
  | zero => simp [fib]
  | succ n ih =>
    have h3 : 3 * (n + 1) = 3 * n + 3 := by ring
    rw [h3, fib_add_three]
    omega
-- BOOK: end fib-even

end Handbook.C12
