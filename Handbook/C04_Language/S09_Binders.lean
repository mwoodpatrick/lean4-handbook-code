/- 第4章 Lean 言語の基礎
   4.7b 引数の3つの括弧 — 明示・暗黙・インスタンス -/
import Mathlib

namespace Handbook.C04

-- BOOK: begin bind-explicit
-- () は明示引数。呼ぶ側が必ず書く
def pairUp (α : Type) (a b : α) : α × α := (a, b)

#check pairUp ℕ 1 2
-- BOOK: end bind-explicit

-- BOOK: begin bind-implicit
-- {} は暗黙引数。他の引数の型から Lean が推論する
def pairUp' {α : Type} (a b : α) : α × α := (a, b)

#check pairUp' 1 2        -- α は ℕ と推論される
#check @pairUp' ℕ 1 2     -- @ を付ければ明示的に渡せる
-- BOOK: end bind-implicit

-- BOOK: begin bind-inst
-- [] はインスタンス引数。型クラスの検索で埋める
def sumPair {α : Type} [Add α] (p : α × α) : α := p.1 + p.2

#eval sumPair (3, 4)
-- BOOK: end bind-inst

-- BOOK: begin bind-variable
-- variable は「以下の宣言で共通に使う引数」をまとめて宣言する
section
variable {G : Type} [Group G]

-- 下の2つはどちらも {G} [Group G] を暗黙に受け取る
theorem inv_inv_self (g : G) : g⁻¹⁻¹ = g := inv_inv g

theorem mul_inv_self (g : G) : g * g⁻¹ = 1 := mul_inv_cancel g

end
-- BOOK: end bind-variable

-- BOOK: begin bind-strict
-- ⦃⦄ は strict implicit。後ろに明示引数が来るまで埋めない
example {α : Type} (f : α → α) (a : α) : α := f a
-- BOOK: end bind-strict

end Handbook.C04
