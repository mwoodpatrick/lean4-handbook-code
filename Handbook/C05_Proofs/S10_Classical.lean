/- 第5章 証明の基本
   5.6 古典論理 — 排中律と背理法 -/
import Mathlib

namespace Handbook.C05

-- BOOK: begin classical-em
-- 排中律: どんな命題も真か偽のどちらかである
example (P : Prop) : P ∨ ¬P := Classical.em P

-- 排中律で場合分けすれば二重否定が消せる
example (P : Prop) (h : ¬¬P) : P := by
  rcases Classical.em P with hp | hnp
  · exact hp
  · exact absurd hnp h
-- BOOK: end classical-em

-- BOOK: begin classical-bycontra
-- 背理法: 結論を否定して矛盾を導く
example (n : ℕ) (h : n ^ 2 ≠ 0) : n ≠ 0 := by
  by_contra hn   -- hn : n = 0(否定の否定は自動で外れる)
  apply h
  rw [hn]
  norm_num
-- BOOK: end classical-bycontra

-- BOOK: begin classical-pushneg
-- push Not は否定を量化子の内側へ押し込んで読める形にする
example : ¬ ∃ m : ℕ, ∀ n : ℕ, n ≤ m := by
  push Not   -- ゴール: ∀ m, ∃ n, m < n
  intro m
  exact ⟨m + 1, Nat.lt_succ_self m⟩
-- BOOK: end classical-pushneg

-- BOOK: begin classical-dne
-- 二重否定除去。構成的論理では証明できない
example (P : Prop) (h : ¬¬P) : P := Classical.byContradiction h

-- Peirce の法則。含意しか含まないのに古典論理を要する
example (P Q : Prop) : ((P → Q) → P) → P := by
  intro h
  by_contra hnp
  exact hnp (h (fun hp => absurd hp hnp))
-- BOOK: end classical-dne

-- BOOK: begin classical-demorgan-quant
-- 量化子版ド・モルガン。→ 向きだけが排中律を要する
example {α : Type} (P : α → Prop) :
    ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := by
  constructor
  · intro h
    by_contra hne
    push Not at hne      -- hne : ∀ x, P x
    exact h hne
  · rintro ⟨x, hx⟩ hall
    exact hx (hall x)
-- BOOK: end classical-demorgan-quant

-- BOOK: begin classical-axioms
-- どの公理に依存したかは #print axioms で監査できる
theorem em_used (P : Prop) : P ∨ ¬P := Classical.em P

#print axioms em_used
-- 出力: 'Handbook.C05.em_used' depends on axioms:
--        [Classical.choice, ...]
-- BOOK: end classical-axioms

end Handbook.C05
