/- English edition source: Handbook/C42_Meta/S03_Elab.lean. -/
import Mathlib

namespace Handbook.C42

open Lean Elab Tactic Meta

-- BOOK: begin elab-hello
-- Build a tactic with elab; this one only displays the goal
elab "show_goal" : tactic => do
  let g ← getMainGoal
  logInfo m!"Current goal: {← g.getType}"

set_option linter.unusedTactic false in
example (a b : ℕ) : a + b = b + a := by
  show_goal
  exact Nat.add_comm a b
-- BOOK: end elab-hello

-- BOOK: begin elab-assumption
-- A tactic of one's own that tries the hypotheses and closes the goal
elab "my_assumption" : tactic => do
  let g ← getMainGoal
  let target ← g.getType
  for decl in ← getLCtx do
    if !decl.isImplementationDetail then
      if ← isDefEq decl.type target then
        g.assign decl.toExpr
        return
  throwError "There is no assumption to apply"

-- Only hq, whose type matches, is used (hp : P is skipped because
-- its type does not match)
example (P Q : Prop) (_hp : P) (hq : Q) : Q := by
  my_assumption
-- BOOK: end elab-assumption

-- BOOK: begin attribute
-- Registering a lemma in the simp set with an attribute (Chapter 41)
@[simp] theorem my_triple (n : ℕ) : 3 * n = n + n + n := by ring

example (n : ℕ) : 3 * n = n + n + n := by simp
-- BOOK: end attribute

-- BOOK: begin debug
-- set_option changes the behavior of the elaborator and the printer
set_option pp.numericTypes true in
#check (2 : ℤ) + 3

-- tracing what simp did
set_option trace.Meta.Tactic.simp true in
example (a : ℕ) : a + 0 = a := by simp
-- BOOK: end debug

end Handbook.C42
