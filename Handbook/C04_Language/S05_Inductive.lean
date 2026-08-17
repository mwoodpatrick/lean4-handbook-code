/- 第4章 Lean 言語の基礎
   4.5 帰納型と再帰 -/
import Mathlib

namespace Handbook.C04

-- BOOK: begin ind-weekday
-- 有限個の値からなる型を自分で定義する
inductive Weekday where
  | monday | tuesday | wednesday | thursday | friday
  | saturday | sunday
  deriving Repr, DecidableEq

def Weekday.isHoliday : Weekday → Bool
  | .saturday | .sunday => true
  | _ => false

#eval Weekday.saturday.isHoliday  -- 出力: true
-- BOOK: end ind-weekday

-- BOOK: begin ind-bool
-- Bool さえ、2つの構成子を持つ普通の帰納型である
def myNot : Bool → Bool
  | true => false
  | false => true

#eval myNot true          -- 出力: false
#eval myNot (myNot true)  -- 出力: true(2回で元に戻る)
-- BOOK: end ind-bool

-- BOOK: begin ind-nat
-- 自然数もライブラリの中で同じ仕組みで定義されている
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

def MyNat.toNat : MyNat → ℕ
  | .zero => 0
  | .succ m => m.toNat + 1

#eval (MyNat.succ (.succ .zero)).toNat  -- 出力: 2
-- BOOK: end ind-nat

-- BOOK: begin ind-tree
-- 二分木。「葉」か「節」の2通りの作り方で尽きる。
inductive Tree where
  | leaf : Tree
  | node : Tree → Tree → Tree

def Tree.leaves : Tree → ℕ
  | .leaf => 1
  | .node l r => l.leaves + r.leaves

#eval (Tree.node (.node .leaf .leaf) .leaf).leaves  -- 出力: 3
-- BOOK: end ind-tree

-- BOOK: begin ind-option
-- Option は「値がない場合がある」ことを型で表す帰納型
#eval [1, 2, 3].head?               -- 出力: some 1
#eval ([] : List ℕ).head?           -- 出力: none
#eval (List.range 10).find? (· > 6) -- 出力: some 7
-- BOOK: end ind-option

end Handbook.C04
