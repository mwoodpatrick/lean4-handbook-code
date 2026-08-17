/- 第5章 証明の基本
   5.5b パターン記法 — rcases / obtain / rintro の共通言語 -/
import Mathlib

namespace Handbook.C05

-- BOOK: begin pat-anon
-- ⟨ ⟩ は「組を作る」と「組を壊す」の両方に使う
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := ⟨hp, hq⟩

-- 右結合なので ⟨hp, hq, hr⟩ は ⟨hp, ⟨hq, hr⟩⟩ の略
example (P Q R : Prop) (h : P ∧ Q ∧ R) : R ∧ P := by
  obtain ⟨hp, _, hr⟩ := h
  exact ⟨hr, hp⟩
-- BOOK: end pat-anon

-- BOOK: begin pat-or
-- | は選言の分岐。枝の数だけ縦棒で区切る
example (P Q R : Prop) (h : P ∨ Q ∨ R) : R ∨ Q ∨ P := by
  rcases h with hp | hq | hr
  · exact Or.inr (Or.inr hp)
  · exact Or.inr (Or.inl hq)
  · exact Or.inl hr
-- BOOK: end pat-or

-- BOOK: begin pat-mixed
-- 積と和は入れ子にできる。形が仮定の形と一致していればよい
example (P Q R : Prop) (h : (P ∧ Q) ∨ R) : P ∨ R := by
  rcases h with ⟨hp, _⟩ | hr
  · exact Or.inl hp
  · exact Or.inr hr
-- BOOK: end pat-mixed

-- BOOK: begin pat-rfl
-- rfl パターンは等式の仮定をその場で消費して変数を消す
example (a b : ℕ) (h : ∃ k, a = b + k) : b ≤ a := by
  obtain ⟨k, rfl⟩ := h
  exact Nat.le_add_right b k
-- BOOK: end pat-rfl

-- BOOK: begin pat-rintro
-- rintro は intro と rcases の合成。取ると同時に分解する
example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  rintro ⟨hp, hq⟩
  exact ⟨hq, hp⟩

-- 使わない部品は _ で捨てる(名前を付けると未使用警告が出る)
example (P Q : Prop) : P ∧ Q → P := by
  rintro ⟨hp, _⟩
  exact hp
-- BOOK: end pat-rintro

end Handbook.C05
