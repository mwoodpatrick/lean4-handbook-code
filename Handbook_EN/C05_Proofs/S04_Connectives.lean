/- English edition source: Handbook/C05_Proofs/S04_Connectives.lean. -/
import Mathlib

namespace Handbook.C05

-- BOOK: begin conn-and
-- To build an "and" use constructor; to use one, use obtain
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  obtain ⟨hp, hq⟩ := h
  exact ⟨hq, hp⟩
-- BOOK: end conn-and

-- BOOK: begin conn-or
-- Split on an "or" with rcases
example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  rcases h with hp | hq
  · right; exact hp
  · left; exact hq
-- BOOK: end conn-or

-- BOOK: begin conn-not
-- The negation ¬P is shorthand for "P → False"
example (P : Prop) (hp : P) : ¬¬P :=
  fun hnp => hnp hp
-- BOOK: end conn-not

-- BOOK: begin conn-demorgan
-- Example: prove one direction of De Morgan's law using parts only
example (P Q : Prop) : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  · intro h
    constructor
    · intro hp; exact h (Or.inl hp)
    · intro hq; exact h (Or.inr hq)
  · rintro ⟨hnp, hnq⟩ (hp | hq)
    · exact hnp hp
    · exact hnq hq
-- BOOK: end conn-demorgan

-- BOOK: begin conn-iff
-- An equivalence P ↔ Q is a pair of the forward direction mp and the
-- reverse mpr
example (P Q : Prop) (h : P ↔ Q) (hp : P) : Q := h.mp hp
-- BOOK: end conn-iff

end Handbook.C05
