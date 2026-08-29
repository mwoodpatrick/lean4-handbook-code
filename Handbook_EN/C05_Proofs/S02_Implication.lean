/- English edition source: Handbook/C05_Proofs/S02_Implication.lean. -/
import Mathlib

namespace Handbook.C05

-- BOOK: begin imp-fun
-- A proof of the implication P → Q is "a function from a proof of P to
-- a proof of Q"
example (P : Prop) : P → P :=
  fun hp => hp

-- The syllogism is nothing but function composition
example (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) : P → R :=
  fun hp => h2 (h1 hp)
-- BOOK: end imp-fun

-- BOOK: begin imp-contrapose
-- Contrapositive: from P → Q we get ¬Q → ¬P (mt = modus tollens)
example (P Q : Prop) (h : P → Q) : ¬Q → ¬P :=
  mt h

-- In tactic mode, contrapose! switches to "prove the contrapositive".
-- We show "if n² is even then n is even" via "if n is odd then n² is
-- odd".
example (n : ℕ) (h : n ^ 2 % 2 = 0) : n % 2 = 0 := by
  contrapose! h
  have h1 : n % 2 = 1 := by omega
  rw [Nat.pow_mod, h1]
  norm_num
-- BOOK: end imp-contrapose

-- BOOK: begin imp-curry
-- With two hypotheses, bundling them with "and" or lining up two arrows
-- is equivalent
example (P Q R : Prop) : (P ∧ Q → R) ↔ (P → Q → R) := by
  constructor
  · intro h hp hq
    exact h ⟨hp, hq⟩
  · rintro h ⟨hp, hq⟩
    exact h hp hq

-- Arrows are right-associative. P → Q → R means P → (Q → R).
example (P Q R : Prop) (h : P → Q → R) (hp : P) : Q → R := h hp
-- BOOK: end imp-curry

end Handbook.C05
