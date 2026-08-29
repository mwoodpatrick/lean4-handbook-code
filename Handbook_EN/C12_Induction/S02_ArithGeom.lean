/- English edition source: Handbook/C12_Induction/S02_ArithGeom.lean. -/
import Mathlib

namespace Handbook.C12

-- BOOK: begin arith-def
-- Define the arithmetic progression with first term a and common
-- difference d by a recurrence
def arith (a d : ℚ) : ℕ → ℚ
  | 0 => a
  | n + 1 => arith a d n + d
-- BOOK: end arith-def

-- BOOK: begin arith-closed
-- The general term aₙ = a + n d. Induction ties the recursive
-- definition to the closed formula.
theorem arith_eq (a d : ℚ) (n : ℕ) :
    arith a d n = a + n * d := by
  induction n with
  | zero => simp [arith]
  | succ n ih =>
    simp only [arith, ih]
    push_cast
    ring
-- BOOK: end arith-closed

-- BOOK: begin geom-def
-- A geometric progression is written in the same shape
def geom (a r : ℚ) : ℕ → ℚ
  | 0 => a
  | n + 1 => geom a r n * r

theorem geom_eq (a r : ℚ) (n : ℕ) :
    geom a r n = a * r ^ n := by
  induction n with
  | zero => simp [geom]
  | succ n ih =>
    simp only [geom, ih]
    ring
-- BOOK: end geom-def

end Handbook.C12
