/- English edition source: Handbook/C07_Equations/S03_Linarith.lean. -/
import Mathlib

namespace Handbook.C07

-- BOOK: begin lin-basic
-- linarith automatically closes combinations of linear inequalities
example (x : ℚ) (h : 2 * x + 3 < 11) : x < 4 := by linarith

example (x y : ℚ) (h1 : x + 2 * y ≤ 4) (h2 : 1 ≤ y) :
    x ≤ 2 := by linarith
-- BOOK: end lin-basic

-- BOOK: begin lin-chain
-- A chain of transitivity in one move
example (a b c d : ℚ) (h1 : a < b) (h2 : b ≤ c) (h3 : c < d) :
    a < d := by linarith
-- BOOK: end lin-chain

-- BOOK: begin lin-mul
-- A product takes it outside linarith's range;
-- inequality × positive number needs a dedicated lemma
example (a b c : ℚ) (h : a < b) (hc : 0 < c) :
    a * c < b * c :=
  mul_lt_mul_of_pos_right h hc

-- adding to or subtracting from both sides stays inside linarith
example (a b : ℚ) (h : a < b) : a + 5 < b + 5 := by linarith
-- BOOK: end lin-mul

end Handbook.C07
