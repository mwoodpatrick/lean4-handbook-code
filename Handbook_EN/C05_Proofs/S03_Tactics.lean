/- English edition source: Handbook/C05_Proofs/S03_Tactics.lean. -/
import Mathlib

namespace Handbook.C05

-- BOOK: begin tac-first
-- Everything after by is tactic mode. We transform the goal
-- interactively.
example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  apply h
  exact hp
-- BOOK: end tac-first

-- BOOK: begin tac-intro
-- intro takes in the hypothesis of an "implies"
example (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) : P → R := by
  intro hp
  apply h2
  apply h1
  exact hp
-- BOOK: end tac-intro

-- BOOK: begin tac-have
-- have sets up an intermediate goal, and suffices declares "this is
-- enough"
example (a b : ℕ) (h : a = b) : a + a = b + b := by
  have h2 : a + a = a + b := by rw [h]
  rw [h2, h]

example (P Q R : Prop) (hpq : P → Q) (hqr : Q → R)
    (hp : P) : R := by
  suffices hq : Q by exact hqr hq
  exact hpq hp
-- BOOK: end tac-have

end Handbook.C05
