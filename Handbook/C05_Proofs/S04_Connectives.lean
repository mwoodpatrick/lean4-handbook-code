/- 第5章 証明の基本
   5.4 論理結合子 -/
import Mathlib

namespace Handbook.C05

-- BOOK: begin conn-and
-- 「かつ」を作るには constructor、使うには obtain
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  obtain ⟨hp, hq⟩ := h
  exact ⟨hq, hp⟩
-- BOOK: end conn-and

-- BOOK: begin conn-or
-- 「または」は rcases で場合分けする
example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  rcases h with hp | hq
  · right; exact hp
  · left; exact hq
-- BOOK: end conn-or

-- BOOK: begin conn-not
-- 否定 ¬P は「P → False」の略記である
example (P : Prop) (hp : P) : ¬¬P :=
  fun hnp => hnp hp
-- BOOK: end conn-not

-- BOOK: begin conn-demorgan
-- 例題: ド・モルガンの法則(の片方)を部品だけで示す
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
-- 同値 P ↔ Q は往路 mp と復路 mpr の組
example (P Q : Prop) (h : P ↔ Q) (hp : P) : Q := h.mp hp
-- BOOK: end conn-iff

end Handbook.C05
