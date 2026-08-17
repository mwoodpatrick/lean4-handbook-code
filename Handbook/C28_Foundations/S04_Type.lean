/- 第28章 数学基礎論と公理的集合論
   28.7 型理論と CIC — Lean の基礎 -/
import Mathlib

namespace Handbook.C28

-- BOOK: begin type-axioms
-- Lean の土台にある公理はこの3つだけ。
-- 命題の外延性(同値な命題は等しい)
#check @propext

-- 商の健全性(同じ類なら等しい)
#check @Quot.sound

-- 選択公理(空でない型から元を取り出す)
#check @Classical.choice
-- BOOK: end type-axioms

-- BOOK: begin type-prop
-- Prop は「命題の宇宙」。証明無関係(proof irrelevance)が成り立ち、
-- 同じ命題の2つの証明は定義的に等しい
example (p : Prop) (h1 h2 : p) : h1 = h2 := rfl

-- Type は「データの宇宙」。こちらは証明無関係でない
#check @Nat
#check @Prop
-- BOOK: end type-prop

-- BOOK: begin type-noncomputable
-- 選択公理を使う定義は計算手続きを持たない。
-- noncomputable がその印である
noncomputable def pick (α : Type) (h : Nonempty α) : α :=
  Classical.choice h

-- 依存関数型: 戻り値の型が引数に依存する。
-- ZFC の関数(順序対の集合)にはない表現力である
#check @Vector
-- BOOK: end type-noncomputable

end Handbook.C28
