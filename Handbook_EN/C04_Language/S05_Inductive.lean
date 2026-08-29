/- English edition source: Handbook/C04_Language/S05_Inductive.lean. -/
import Mathlib

namespace Handbook.C04

-- BOOK: begin ind-weekday
-- We define our own type consisting of finitely many values
inductive Weekday where
  | monday | tuesday | wednesday | thursday | friday
  | saturday | sunday
  deriving Repr, DecidableEq

def Weekday.isHoliday : Weekday → Bool
  | .saturday | .sunday => true
  | _ => false

#eval Weekday.saturday.isHoliday  -- output: true
-- BOOK: end ind-weekday

-- BOOK: begin ind-bool
-- Even Bool is an ordinary inductive type with two constructors
def myNot : Bool → Bool
  | true => false
  | false => true

#eval myNot true          -- output: false
-- output: true (two applications return the original)
#eval myNot (myNot true)
-- BOOK: end ind-bool

-- BOOK: begin ind-nat
-- The natural numbers are defined in the library by the same mechanism
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

def MyNat.toNat : MyNat → ℕ
  | .zero => 0
  | .succ m => m.toNat + 1

#eval (MyNat.succ (.succ .zero)).toNat  -- output: 2
-- BOOK: end ind-nat

-- BOOK: begin ind-tree
-- A binary tree. Exhausted by two ways of building: a "leaf" or a
-- "node".
inductive Tree where
  | leaf : Tree
  | node : Tree → Tree → Tree

def Tree.leaves : Tree → ℕ
  | .leaf => 1
  | .node l r => l.leaves + r.leaves

#eval (Tree.node (.node .leaf .leaf) .leaf).leaves  -- output: 3
-- BOOK: end ind-tree

-- BOOK: begin ind-option
-- Option is an inductive type expressing in the type that "a value may
-- be absent"
#eval [1, 2, 3].head?               -- output: some 1
#eval ([] : List ℕ).head?           -- output: none
#eval (List.range 10).find? (· > 6) -- output: some 7
-- BOOK: end ind-option

end Handbook.C04
