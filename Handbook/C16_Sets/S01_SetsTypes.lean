/- 第16章 集合と写像 — 数学の言語
   16.1 集合と型 — Lean における2つの「集まり」 -/
import Mathlib

namespace Handbook.C16

-- BOOK: begin set-def
-- Set α の正体は「α 上の述語」である(Set α := α → Prop)
def evens : Set ℕ := {n | n % 2 = 0}

-- 所属 x ∈ S とは、述語 S x が成り立つこと
example : 4 ∈ evens := rfl

example : 7 ∉ evens := by simp [evens]
-- BOOK: end set-def

-- BOOK: begin set-vs-type
-- 型は「世界」、集合は「世界の中の範囲」
#check ℕ            -- 型
#check evens        -- Set ℕ(ℕ という世界の中の範囲)
#check {n : ℕ | n % 2 = 0}  -- 内包記法
-- BOOK: end set-vs-type

-- BOOK: begin set-subset
-- 部分集合 ⊆ は「所属の含意」そのもの
example : evens ⊆ {n : ℕ | n % 2 = 0} := fun _ h => h

-- 内包記法での所属は、定義的に述語の成立と同じ(Iff.rfl で閉じる)
example (n : ℕ) : n ∈ {m : ℕ | m % 2 = 0} ↔ n % 2 = 0 := Iff.rfl
-- BOOK: end set-subset

end Handbook.C16
