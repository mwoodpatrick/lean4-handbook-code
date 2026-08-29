/- Chapter 7: Equations and inequalities
   7.3 Cubic equations -/
import Mathlib

namespace Handbook.C07

-- BOOK: begin cubic-depressed
-- The substitution x = y - b/3 removes the quadratic term
example (b c d y : ℝ) :
    (y - b / 3) ^ 3 + b * (y - b / 3) ^ 2 + c * (y - b / 3) + d
      = y ^ 3 + (c - b ^ 2 / 3) * y
        + (d - b * c / 3 + 2 * b ^ 3 / 27) := by
  ring
-- BOOK: end cubic-depressed

-- BOOK: begin cubic-cardano
-- Cardano: write the root as a sum u + v with u^3 + v^3 = -q
-- and 3uv = -p, and the cubic collapses
example (p q u v : ℝ) (h1 : u ^ 3 + v ^ 3 = -q)
    (h2 : 3 * (u * v) = -p) :
    (u + v) ^ 3 + p * (u + v) + q = 0 := by
  have hp : p = -(3 * (u * v)) := by linarith
  subst hp
  linear_combination h1
-- BOOK: end cubic-cardano

-- BOOK: begin cubic-rational
-- In practice: guess a rational root and factor
example (x : ℝ) :
    x ^ 3 - 6 * x ^ 2 + 11 * x - 6 = 0 ↔ x = 1 ∨ x = 2 ∨ x = 3 := by
  constructor
  · intro h
    have hf : (x - 1) * ((x - 2) * (x - 3)) = 0 := by
      linear_combination h
    rcases mul_eq_zero.mp hf with h1 | h1
    · left; linarith
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · right; left; linarith
      · right; right; linarith
  · rintro (rfl | rfl | rfl) <;> norm_num
-- BOOK: end cubic-rational

end Handbook.C07
