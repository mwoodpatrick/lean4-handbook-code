/- 第42章 メタプログラミングと tactic 開発
   42.4 elab による tactic 自作 / 42.5 属性 / 42.6 デバッグ -/
import Mathlib

namespace Handbook.C42

open Lean Elab Tactic Meta

-- BOOK: begin elab-hello
-- elab で tactic を作る。ゴールを表示するだけの tactic
elab "show_goal" : tactic => do
  let g ← getMainGoal
  logInfo m!"現在のゴール: {← g.getType}"

set_option linter.unusedTactic false in
example (a b : ℕ) : a + b = b + a := by
  show_goal
  exact Nat.add_comm a b
-- BOOK: end elab-hello

-- BOOK: begin elab-assumption
-- 仮定を順に試して閉じる tactic を自作する
elab "my_assumption" : tactic => do
  let g ← getMainGoal
  let target ← g.getType
  for decl in ← getLCtx do
    if !decl.isImplementationDetail then
      if ← isDefEq decl.type target then
        g.assign decl.toExpr
        return
  throwError "当てはまる仮定がない"

-- 型の合う hq だけが選ばれる(hp : P は型が合わないので飛ばす)
example (P Q : Prop) (_hp : P) (hq : Q) : Q := by
  my_assumption
-- BOOK: end elab-assumption

-- BOOK: begin attribute
-- 属性で simp set に登録する(第41章)
@[simp] theorem my_triple (n : ℕ) : 3 * n = n + n + n := by ring

example (n : ℕ) : 3 * n = n + n + n := by simp
-- BOOK: end attribute

-- BOOK: begin debug
-- set_option でカーネルや elaborator の挙動を覗く
set_option pp.numericTypes true in
#check (2 : ℤ) + 3

-- trace で simp が使った補題を追う
set_option trace.Meta.Tactic.simp true in
example (a : ℕ) : a + 0 = a := by simp
-- BOOK: end debug

end Handbook.C42
