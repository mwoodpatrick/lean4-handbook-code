/- 第5章 証明の基本
   5.3 tactic モード入門 -/
import Mathlib

namespace Handbook.C05

-- BOOK: begin tac-first
-- by 以降が tactic モード。ゴールを対話的に変形する。
example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  apply h
  exact hp
-- BOOK: end tac-first

-- BOOK: begin tac-intro
-- intro は「ならば」の仮定を取り込む
example (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) : P → R := by
  intro hp
  apply h2
  apply h1
  exact hp
-- BOOK: end tac-intro

-- BOOK: begin tac-have
-- have は中間目標を立て、suffices は「これで十分」と宣言する
example (a b : ℕ) (h : a = b) : a + a = b + b := by
  have h2 : a + a = a + b := by rw [h]
  rw [h2, h]

example (P Q R : Prop) (hpq : P → Q) (hqr : Q → R)
    (hp : P) : R := by
  suffices hq : Q by exact hqr hq
  exact hpq hp
-- BOOK: end tac-have

end Handbook.C05
