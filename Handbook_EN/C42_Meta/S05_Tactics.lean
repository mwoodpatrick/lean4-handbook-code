/- English edition source: Handbook/C42_Meta/S05_Tactics.lean. -/
import Mathlib

namespace Handbook.C42

open Lean Elab Tactic Meta

-- BOOK: begin tactic-combinator
-- first picks the first tactic that succeeds.
-- The goal is nonlinear, so omega fails and ring is taken.
example (a b : ℤ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  first
  | omega
  | ring

-- <;> applies the same tactic to every resulting goal
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor <;> assumption

-- repeat runs a tactic until it fails
example (a b c : ℕ) : a + 0 + (b + 0) + (c + 0) = a + b + c := by
  repeat rw [Nat.add_zero]
-- BOOK: end tactic-combinator

-- BOOK: begin tactic-try
-- try swallows a failure, so it can be applied to all goals
example (p : Prop) (hp : p) : p ∧ (2 = 2) := by
  constructor
  all_goals try assumption
  rfl
-- BOOK: end tactic-try

-- BOOK: begin elab-count
-- A tactic that counts the hypotheses and reports the number
elab "count_hyps" : tactic => do
  let mut n : Nat := 0
  for d in ← getLCtx do
    if !d.isImplementationDetail then
      n := n + 1
  logInfo m!"Number of assumptions: {n}"

set_option linter.unusedTactic false in
example (a b : ℕ) (_h1 : a = b) (_h2 : b = a) : True := by
  count_hyps
  trivial
-- BOOK: end elab-count

-- BOOK: begin elab-with-arg
-- A tactic taking an argument: receive a term and hand it to exact
elab "my_exact " t:term : tactic => do
  let g ← getMainGoal
  let e ← elabTerm t (← g.getType)
  g.assign e

example (p : Prop) (hp : p) : p := by
  my_exact hp
-- BOOK: end elab-with-arg

-- BOOK: begin meta-mkapp
-- Building terms in MetaM; mkAppM infers the implicit arguments
def buildRefl (e : Expr) : MetaM Expr :=
  mkAppM ``Eq.refl #[e]

#eval show MetaM Unit from do
  let e ← mkAppM ``Nat.succ #[mkNatLit 3]
  let r ← buildRefl e
  logInfo m!"{← inferType r}"
-- BOOK: end meta-mkapp

end Handbook.C42
