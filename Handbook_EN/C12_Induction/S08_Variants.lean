/- English edition source: Handbook/C12_Induction/S08_Variants.lean. -/
import Mathlib

namespace Handbook.C12

-- BOOK: begin var-from
-- Induction starting partway along, for a claim holding only for n ≥ 5
example (n : ℕ) (hn : 5 ≤ n) : 2 ^ n > n ^ 2 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h1 : 1 ≤ n := by omega
    calc 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      _ > 2 * n ^ 2 := by omega
      _ ≥ (n + 1) ^ 2 := by nlinarith
-- BOOK: end var-from

-- BOOK: begin var-list
-- Structural induction, following the shape of a list
example (l : List ℕ) : l.reverse.length = l.length := by
  induction l with
  | nil => rfl
  | cons a t ih => simp
-- BOOK: end var-list

-- BOOK: begin var-two
-- Induction using two steps back, matching a Fibonacci-type
-- recurrence
example (n : ℕ) : Nat.fib n ≤ 2 ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num
  | one => norm_num
  | more n ih1 ih2 =>
    rw [Nat.fib_add_two]
    calc Nat.fib n + Nat.fib (n + 1) ≤ 2 ^ n + 2 ^ (n + 1) := by
          omega
      _ ≤ 2 ^ (n + 2) := by ring_nf; omega
-- BOOK: end var-two

end Handbook.C12
