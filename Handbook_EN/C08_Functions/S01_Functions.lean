/- Chapter 8: The basics of functions
   8.1 What is a function? -- from correspondence to map -/
import Mathlib

namespace Handbook.C08

-- BOOK: begin fun-def
def f (x : ℚ) : ℚ := 2 * x + 1

#eval f 3  -- output: 7

-- Equality of functions means agreeing at every input (extensionality)
example : (fun x : ℚ => x + x) = fun x => 2 * x := by
  funext x
  ring
-- BOOK: end fun-def

-- BOOK: begin fun-ext
-- Two functions whose expansions agree are equal as functions
example : (fun x : ℚ => (x + 1) ^ 2) =
    (fun x : ℚ => x ^ 2 + 2 * x + 1) := by
  funext x
  ring
-- BOOK: end fun-ext

-- BOOK: begin fun-shift
-- Shifting a graph is pre- and post-processing of input and output
def g0 (x : ℚ) : ℚ := x ^ 2

def gShift (x : ℚ) : ℚ := g0 (x - 2) + 3

#eval gShift 2  -- output: 3 (the vertex (0,0) moved to (2,3))
#eval gShift 4  -- output: 7 (= g0 2 + 3)

-- symmetric in the y axis (even): the sign of the input does not matter
example (x : ℚ) : g0 (-x) = g0 x := by
  unfold g0; ring
-- the minimum after the shift: the vertex (2, 3) is the lowest point
example (x : ℚ) : 3 ≤ gShift x := by
  unfold gShift g0
  nlinarith [sq_nonneg (x - 2)]
-- BOOK: end fun-shift

-- BOOK: begin fun-parity
-- Even functions f(−x) = f(x) and odd functions f(−x) = −f(x)
example (x : ℚ) : (-x) ^ 2 = x ^ 2 := by ring

example (x : ℚ) : (-x) ^ 3 = -(x ^ 3) := by ring
-- BOOK: end fun-parity

-- BOOK: begin fun-gallery
-- A function needing care about its domain:
-- √ returns the junk value 0 on negative input
example : Real.sqrt (-4) = 0 := by
  rw [Real.sqrt_eq_zero']
  norm_num

-- The identity: a function that does nothing is a function all the same
example (x : ℚ) : id x = x := rfl
example : Function.Injective (id : ℚ → ℚ) := fun a b h => h
-- BOOK: end fun-gallery

end Handbook.C08
