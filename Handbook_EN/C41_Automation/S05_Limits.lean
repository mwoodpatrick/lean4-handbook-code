/- English edition source: Handbook/C41_Automation/S05_Limits.lean. -/
import Mathlib

namespace Handbook.C41

-- BOOK: begin limit-omega
-- omega decides goals in linear integer arithmetic
example (n m : ℕ) (h : 2 * n + 3 * m = 12) (h2 : m = 2) : n = 3 := by
  omega

-- With a product it is no longer linear, so omega gives up.
-- Hand nlinarith an auxiliary term and it closes the goal.
example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ x * y := by
  positivity
-- BOOK: end limit-omega

-- BOOK: begin limit-ring
-- ring closes equations of a commutative ring, but not inequalities
example (a b : ℤ) : (a - b) * (a + b) = a ^ 2 - b ^ 2 := by ring

-- Inequalities are the domain of linarith; equalities and inequalities
-- call for different tools.
example (a b : ℝ) (h : a ≤ b) : a - b ≤ 0 := by linarith
-- BOOK: end limit-ring

-- BOOK: begin limit-decide
-- decide closes it when the range is finite
example : ∀ n : Fin 4, n.val < 4 := by decide

-- An unbounded claim is not closed by decide;
-- use recursion or an existing lemma
example : ∀ n : ℕ, 0 ≤ n := fun n => Nat.zero_le n
-- BOOK: end limit-decide

-- BOOK: begin limit-simp
-- simp rewrites, and only with rules that have a fixed direction
example (l : List ℕ) : (l ++ []).length = l.length := by simp

-- ring and abel are the tools for algebraic identities
example (a b : ℤ) : a + b = b + a := by ring
-- BOOK: end limit-simp

end Handbook.C41
