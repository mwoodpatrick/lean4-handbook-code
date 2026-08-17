/- 第42章 メタプログラミングと tactic 開発
   42.9 実用的な tactic を書く -/
import Mathlib

namespace Handbook.C42

open Lean Elab Tactic Meta

-- BOOK: begin tactic-combinator
-- tactic の組み合わせ子。first は最初に成功したものを採る。
-- omega は非線形なので失敗し、ring が引き受ける
example (a b : ℤ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  first
  | omega
  | ring

-- <;> は全てのゴールに同じ tactic を当てる
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor <;> assumption

-- repeat は失敗するまで繰り返す
example (a b c : ℕ) : a + 0 + (b + 0) + (c + 0) = a + b + c := by
  repeat rw [Nat.add_zero]
-- BOOK: end tactic-combinator

-- BOOK: begin tactic-try
-- try は失敗を握りつぶす。all_goals と組むと安全に走らせられる
example (p : Prop) (hp : p) : p ∧ (2 = 2) := by
  constructor
  all_goals try assumption
  rfl
-- BOOK: end tactic-try

-- BOOK: begin elab-count
-- 仮定の個数を数えて報告する tactic
elab "count_hyps" : tactic => do
  let mut n : Nat := 0
  for d in ← getLCtx do
    if !d.isImplementationDetail then
      n := n + 1
  logInfo m!"仮定の個数: {n}"

set_option linter.unusedTactic false in
example (a b : ℕ) (_h1 : a = b) (_h2 : b = a) : True := by
  count_hyps
  trivial
-- BOOK: end elab-count

-- BOOK: begin elab-with-arg
-- 引数を取る tactic。term を受け取って exact に渡す
elab "my_exact " t:term : tactic => do
  let g ← getMainGoal
  let e ← elabTerm t (← g.getType)
  g.assign e

example (p : Prop) (hp : p) : p := by
  my_exact hp
-- BOOK: end elab-with-arg

-- BOOK: begin meta-mkapp
-- MetaM で項を組み立てる。mkAppM は暗黙引数を推論させる
def buildRefl (e : Expr) : MetaM Expr :=
  mkAppM ``Eq.refl #[e]

#eval show MetaM Unit from do
  let e ← mkAppM ``Nat.succ #[mkNatLit 3]
  let r ← buildRefl e
  logInfo m!"{← inferType r}"
-- BOOK: end meta-mkapp

end Handbook.C42
