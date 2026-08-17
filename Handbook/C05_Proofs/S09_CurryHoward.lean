/- 第5章 証明の基本
   5.9 Curry–Howard 同型 — 証明とプログラムは同じものである -/
import Mathlib

namespace Handbook.C05

-- BOOK: begin ch-pairs
-- 「P かつ Q の証明」は「P の証明と Q の証明の組」そのもの
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := ⟨hp, hq⟩

-- 「P ならば Q の証明」は「P の証明を Q の証明へ写す関数」
example (P : Prop) : P → P ∧ P := fun hp => ⟨hp, hp⟩

-- 存在の証明は「証拠と、その証拠が条件を満たす証明」の組
example : ∃ n : ℕ, n + 1 = 4 := ⟨3, rfl⟩
-- BOOK: end ch-pairs

-- BOOK: begin proofs-exercises
-- 演習: 本章の部品だけで証明できる3問
example (P Q : Prop) (h : P ∧ Q) : P ∨ Q := Or.inl h.1

example (P : Prop) : ¬(P ∧ ¬P) := fun ⟨hp, hnp⟩ => hnp hp

example : ∃ n : ℕ, 2 * n = 10 := ⟨5, rfl⟩
-- BOOK: end proofs-exercises

end Handbook.C05
