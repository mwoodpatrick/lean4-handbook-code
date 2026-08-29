/- Chapter 17: Real numbers and limits of sequences
   17.3 Convergence of sequences -- reading and writing the ε-N definition -/
import Mathlib

namespace Handbook.C17

-- BOOK: begin epsn-def
-- Write the ε-N definition down exactly as it stands
def TendsToNat (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε
-- BOOK: end epsn-def

-- BOOK: begin epsn-proof
-- Prove 1/(n+1) → 0 straight from the definition
theorem one_div_tendsTo_zero :
    TendsToNat (fun n => 1 / (n + 1)) 0 := by
  intro ε hε
  -- The Archimedean property: pick a natural number N exceeding 1/ε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  use N
  intro n hn
  have h1 : (0 : ℝ) < n + 1 := by positivity
  rw [sub_zero, abs_of_pos (by positivity), div_lt_iff₀ h1]
  -- BOOK: elide begin from 1/ε < N ≤ n < n+1 we get 1 < ε(n+1)
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : 1 / ε < (n : ℝ) + 1 := by linarith
  rw [div_lt_iff₀ hε] at h2
  exact h2.trans_eq (mul_comm _ _)
  -- BOOK: elide end
-- BOOK: end epsn-proof

-- BOOK: begin epsn-const
-- The constant sequence c, c, c, … converges to c (any N will do)
example (c : ℝ) : TendsToNat (fun _ => c) c := by
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  simpa using hε
-- BOOK: end epsn-const

end Handbook.C17
