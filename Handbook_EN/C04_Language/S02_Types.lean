/- English edition source: Handbook/C04_Language/S02_Types.lean. -/
import Mathlib

namespace Handbook.C04

-- BOOK: begin types-fun
def double (n : ℕ) : ℕ := 2 * n

#check double    -- double : ℕ → ℕ
#eval double 21  -- output: 42
-- BOOK: end types-fun

-- BOOK: begin types-curry
-- A multi-argument function is a "function that returns a function"
-- (currying)
def add3 (a b c : ℕ) : ℕ := a + b + c

#check add3      -- add3 : ℕ → ℕ → ℕ → ℕ
#check add3 1    -- add3 1 : ℕ → ℕ → ℕ (partial application)
#eval add3 1 2 3 -- output: 6
-- BOOK: end types-curry

-- BOOK: begin types-lambda
-- An anonymous function (lambda expression). fun argument => body.
#eval (fun x : ℕ => x ^ 2) 9          -- output: 81
#eval [1, 2, 3].map (fun n => n * n)  -- output: [1, 4, 9]

-- Function composition ∘ : (f ∘ g) x = f (g x)
#eval (double ∘ double) 3  -- output: 12
-- BOOK: end types-lambda

-- BOOK: begin types-hof
-- A function that takes a function (a higher-order function)
#eval [1, 2, 3, 4, 5].filter (· % 2 = 1)  -- output: [1, 3, 5]
#eval [1, 2, 3, 4].foldl (· + ·) 0        -- output: 10
#eval (List.range 6).map (2 ^ ·)          -- [1, 2, 4, …, 32]
-- BOOK: end types-hof

-- BOOK: begin types-type
-- Types themselves are expressions, and they have types too
#check ℕ     -- ℕ : Type
#check Type  -- Type : Type 1
-- BOOK: end types-type

end Handbook.C04
