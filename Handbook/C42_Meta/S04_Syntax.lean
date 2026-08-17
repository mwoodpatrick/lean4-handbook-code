/- 第42章 メタプログラミングと tactic 開発
   42.7 記法の定義 / 42.8 syntax カテゴリ -/
import Mathlib

namespace Handbook.C42

open Lean

-- BOOK: begin notation-basic
-- notation で中置記法を定義する。優先順位を数で与える
notation:65 a " ⊕ᵢ " b => Nat.max a b

example : (3 ⊕ᵢ 5) = 5 := rfl
-- BOOK: end notation-basic

-- BOOK: begin notation-prefix
-- 前置記法。既存の記号(‖ など)と衝突しない綴りを選ぶ
prefix:max "S!" => Nat.succ

example : S!(3 : ℕ) = 4 := by decide
-- BOOK: end notation-prefix

-- BOOK: begin syntax-decl
-- syntax で構文だけを宣言し、macro_rules で意味を与える。
-- term:max にしないと twice 5 = 10 が twice (5 = 10) になる
syntax:max "twice " term:max : term

macro_rules
  | `(twice $x) => `($x + $x)

example : twice 5 = 10 := rfl
-- BOOK: end syntax-decl

-- BOOK: begin macro-recursive
-- 再帰的なマクロ。区切り記号で任意個の引数を受ける
syntax "maxOf[" term,* "]" : term

macro_rules
  | `(maxOf[]) => `(0)
  | `(maxOf[$x]) => `($x)
  | `(maxOf[$x, $xs,*]) => `(Nat.max $x (maxOf[$xs,*]))

example : maxOf[3, 7, 2] = 7 := rfl
-- BOOK: end macro-recursive

-- BOOK: begin macro-tactic
-- tactic もマクロで作れる。既存の tactic の組み合わせに名前を付ける
macro "finish_arith" : tactic =>
  `(tactic| first | omega | simp | ring)

example (n : ℕ) (h : n > 3) : n ≥ 4 := by finish_arith

example (a b : ℤ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  finish_arith
-- BOOK: end macro-tactic

end Handbook.C42
