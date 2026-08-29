/- English edition source: Handbook/C42_Meta/S04_Syntax.lean. -/
import Mathlib

namespace Handbook.C42

open Lean

-- BOOK: begin notation-basic
-- Defining an operator with notation; the number gives its precedence
notation:65 a " ⊕ᵢ " b => Nat.max a b

example : (3 ⊕ᵢ 5) = 5 := rfl
-- BOOK: end notation-basic

-- BOOK: begin notation-prefix
-- Take care to choose a symbol that does not clash with an existing
-- one (‖, for instance)
prefix:max "S!" => Nat.succ

example : S!(3 : ℕ) = 4 := by decide
-- BOOK: end notation-prefix

-- BOOK: begin syntax-decl
-- syntax declares the shape only; macro_rules gives it meaning.
-- term:max binds tightly, so twice 5 = 10 parses as (twice 5) = 10
syntax:max "twice " term:max : term

macro_rules
  | `(twice $x) => `($x + $x)

example : twice 5 = 10 := rfl
-- BOOK: end syntax-decl

-- BOOK: begin macro-recursive
-- Recursive macro: accepts any number of arguments separated by
-- punctuation.
syntax "maxOf[" term,* "]" : term

macro_rules
  | `(maxOf[]) => `(0)
  | `(maxOf[$x]) => `($x)
  | `(maxOf[$x, $xs,*]) => `(Nat.max $x (maxOf[$xs,*]))

example : maxOf[3, 7, 2] = 7 := rfl
-- BOOK: end macro-recursive

-- BOOK: begin macro-tactic
-- naming a combination of existing tactics
macro "finish_arith" : tactic =>
  `(tactic| first | omega | simp | ring)

example (n : ℕ) (h : n > 3) : n ≥ 4 := by finish_arith

example (a b : ℤ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  finish_arith
-- BOOK: end macro-tactic

end Handbook.C42
