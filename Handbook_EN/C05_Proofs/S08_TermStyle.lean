/- English edition source: Handbook/C05_Proofs/S08_TermStyle.lean. -/
import Mathlib

namespace Handbook.C05

-- BOOK: begin term-vs-tactic
-- The same theorem in term style (the proof written directly)
theorem add_pos_term {a b : ℕ} (ha : 0 < a) : 0 < a + b :=
  Nat.lt_of_lt_of_le ha (Nat.le_add_right a b)

-- tactic style (built after by)
theorem add_pos_tactic {a b : ℕ} (ha : 0 < a) : 0 < a + b := by
  omega
-- BOOK: end term-vs-tactic

-- BOOK: begin term-show
-- show ... from ... annotates the type in term style
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q :=
  show P ∧ Q from ⟨hp, hq⟩
-- BOOK: end term-show

end Handbook.C05
