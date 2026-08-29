/- English edition source: Handbook/C04_Language/S03_Defs.lean. -/
import Mathlib

namespace Handbook.C04

-- BOOK: begin defs-if
-- The Collatz map: halve if even, otherwise 3n+1
def collatzStep (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

#eval collatzStep 7   -- output: 22
#eval collatzStep 22  -- output: 11
-- BOOK: end defs-if

-- BOOK: begin defs-rec
-- A recursive definition. The sum from 0 to n.
def sumTo : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumTo n + (n + 1)

#eval sumTo 10  -- output: 55
-- BOOK: end defs-rec

-- BOOK: begin defs-match
-- A match expression splits into cases by pattern
def describe (n : ℕ) : String :=
  match n with
  | 0 => "zero"
  | 1 => "one"
  | _ => "many"

#eval describe 0  -- output: "zero"
#eval describe 7  -- output: "many"
-- BOOK: end defs-match

-- BOOK: begin defs-where
-- Auxiliary definitions can be placed after the body with where
-- (Heron's formula)
def heron2 (a b c : ℚ) : ℚ :=
  s * (s - a) * (s - b) * (s - c)
where
  s : ℚ := (a + b + c) / 2

-- output: 36 (the square of the area; for 3:4:5 the area is 6)
#eval heron2 3 4 5
-- BOOK: end defs-where

-- BOOK: begin defs-listsum
-- Recursion over a list. :: decomposes into "head + rest".
def total : List ℚ → ℚ
  | [] => 0
  | x :: rest => x + total rest

#eval total [1, 2, 3, 4]  -- output: 10
-- BOOK: end defs-listsum

-- BOOK: begin defs-sumto-check
-- A claim about a function we defined is itself a theorem
example : sumTo 100 = 5050 := by rfl
example (n : ℕ) : sumTo (n + 1) = sumTo n + (n + 1) := rfl
-- BOOK: end defs-sumto-check

end Handbook.C04
