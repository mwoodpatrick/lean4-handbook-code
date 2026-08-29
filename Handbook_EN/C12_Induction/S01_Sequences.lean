/- Chapter 12: Sequences and mathematical induction
   12.1 A sequence is a function -/
import Mathlib

namespace Handbook.C12

-- BOOK: begin seq-def
-- The odd numbers in increasing order: a sequence is a function ℕ → ℚ
def oddSeq : ℕ → ℚ := fun n => 2 * n + 1

#eval oddSeq 0  -- output: 1
#eval oddSeq 3  -- output: 7
-- BOOK: end seq-def

-- BOOK: begin seq-mono
-- Monotone increasing, from the comparison of adjacent terms alone
theorem oddSeq_strictMono : StrictMono oddSeq := by
  apply strictMono_nat_of_lt_succ
  intro n
  unfold oddSeq
  push_cast
  linarith
-- BOOK: end seq-mono

-- BOOK: begin seq-bounded
-- Bounded below: every term is at least a fixed constant
theorem oddSeq_bddBelow : ∀ n, (1 : ℚ) ≤ oddSeq n := by
  intro n
  unfold oddSeq
  have hn : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  linarith
-- BOOK: end seq-bounded

-- BOOK: begin seq-anon
-- A sequence not worth naming is written as an anonymous function
#eval (fun n : ℕ => n ^ 2) 5  -- output: 25

example : (fun n : ℕ => (n : ℚ) / (n + 1)) 1 = 1 / 2 := by
  norm_num
-- BOOK: end seq-anon

end Handbook.C12
