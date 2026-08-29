/- English edition source: Handbook/C12_Induction/S05_StrongInduction.lean. -/
import Mathlib

namespace Handbook.C12

-- BOOK: begin strong-ind
-- Every natural number at least 2 has a prime factor.
-- A typical use of strong induction, assuming the claim for every
-- number below n.
theorem exists_prime_factor :
    ∀ n : ℕ, 2 ≤ n → ∃ p, p.Prime ∧ p ∣ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h2
    by_cases hp : n.Prime
    · exact ⟨n, hp, dvd_refl n⟩
    · -- If it is not prime, choose a proper divisor m with 2 ≤ m < n
      obtain ⟨m, hdvd, hm2, hmn⟩ :=
        Nat.exists_dvd_of_not_prime2 h2 hp
      obtain ⟨p, hp, hpm⟩ := ih m hmn hm2
      exact ⟨p, hp, hpm.trans hdvd⟩
-- BOOK: end strong-ind

-- BOOK: begin binary-rep
-- Another face of strong induction: recursion that makes the input
-- smaller by division.
-- A positive natural becomes 0 after division by 2 once per binary
-- digit.
def binLength : ℕ → ℕ
  | 0 => 0
  | n + 1 => binLength ((n + 1) / 2) + 1
decreasing_by
  exact Nat.div_lt_self (Nat.succ_pos n) one_lt_two

#eval binLength 6   -- output: 3 (110₂)
#eval binLength 16  -- output: 5 (10000₂)
-- BOOK: end binary-rep

-- BOOK: begin le-induction
-- Induction starting partway through: n² ≤ 2ⁿ for n ≥ 4
theorem sq_le_two_pow {n : ℕ} (hn : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h1 : (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
    calc (n + 1) ^ 2 ≤ 2 * n ^ 2 := h1
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (n + 1) := by rw [pow_succ]; ring
-- BOOK: end le-induction

end Handbook.C12
