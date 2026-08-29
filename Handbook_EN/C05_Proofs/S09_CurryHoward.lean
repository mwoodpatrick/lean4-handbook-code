/- English edition source: Handbook/C05_Proofs/S09_CurryHoward.lean. -/
import Mathlib

namespace Handbook.C05

-- BOOK: begin ch-pairs
-- "A proof of P and Q" is exactly "a pair of a proof of P and a proof
-- of Q"
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := ⟨hp, hq⟩

-- "A proof of P implies Q" is "a function mapping a proof of P to a
-- proof of Q"
example (P : Prop) : P → P ∧ P := fun hp => ⟨hp, hp⟩

-- A proof of existence is a pair of "a witness, and a proof that the
-- witness satisfies the condition"
example : ∃ n : ℕ, n + 1 = 4 := ⟨3, rfl⟩
-- BOOK: end ch-pairs

-- BOOK: begin proofs-exercises
-- Exercises: three problems provable with this chapter's parts only
example (P Q : Prop) (h : P ∧ Q) : P ∨ Q := Or.inl h.1

example (P : Prop) : ¬(P ∧ ¬P) := fun ⟨hp, hnp⟩ => hnp hp

example : ∃ n : ℕ, 2 * n = 10 := ⟨5, rfl⟩
-- BOOK: end proofs-exercises

end Handbook.C05
