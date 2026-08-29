/- Chapter 6: Numbers and expressions
   6.3 Expanding and factoring -/
import Mathlib

namespace Handbook.C06

-- BOOK: begin ring-expand
-- Expanding and factoring are the same "ring equation" to ring
example (x y : ℚ) :
    (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by ring

example (x y : ℚ) :
    (x + y) * (x - y) = x ^ 2 - y ^ 2 := by ring

example (x : ℚ) :
    x ^ 3 - 1 = (x - 1) * (x ^ 2 + x + 1) := by ring
-- BOOK: end ring-expand

-- BOOK: begin ring-cube3
-- Expanding a cube. The coefficients 1, 3, 3, 1 are the third row
-- of Pascal's triangle.
example (a b : ℚ) :
    (a + b) ^ 3 =
      a ^ 3 + 3 * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3 := by
  ring
-- BOOK: end ring-cube3

-- BOOK: begin ring-mental
-- Mental arithmetic is an identity too: 99² = (100 − 1)²
example (a b : ℤ) :
    (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by ring

example : (99 : ℤ) ^ 2 = 9801 := by norm_num
-- BOOK: end ring-mental

-- BOOK: begin ring-symmetric
-- Three variables are no different; ring takes on all the steps
example (a b c : ℚ) :
    (a + b + c) ^ 2 =
      a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + b * c + c * a) := by
  ring
-- BOOK: end ring-symmetric

-- BOOK: begin ring-identity
-- A famous identity (Brahmagupta--Fibonacci)
example (a b c d : ℚ) :
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) =
      (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 := by ring
-- BOOK: end ring-identity

-- BOOK: begin ring-cube
-- Factoring a sum of cubes
example (x y : ℚ) :
    x ^ 3 + y ^ 3 = (x + y) * (x ^ 2 - x * y + y ^ 2) := by
  ring

-- completing the square
example (x : ℚ) :
    x ^ 2 - 6 * x + 13 = (x - 3) ^ 2 + 4 := by
  ring
-- BOOK: end ring-cube

-- BOOK: begin ring-sophie
-- Sophie Germain's identity: a⁴ + 4b⁴ always factors
example (a b : ℚ) :
    a ^ 4 + 4 * b ^ 4 =
      ((a + b) ^ 2 + b ^ 2) * ((a - b) ^ 2 + b ^ 2) := by
  ring
-- BOOK: end ring-sophie

end Handbook.C06
