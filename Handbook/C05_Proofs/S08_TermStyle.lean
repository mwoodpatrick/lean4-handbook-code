/- 第5章 証明の基本
   5.8 項スタイル証明と tactic スタイル証明 -/
import Mathlib

namespace Handbook.C05

-- BOOK: begin term-vs-tactic
-- 同じ定理を項スタイルで(証明項を直接書く)
theorem add_pos_term {a b : ℕ} (ha : 0 < a) : 0 < a + b :=
  Nat.lt_of_lt_of_le ha (Nat.le_add_right a b)

-- tactic スタイルで(by 以降で構築する)
theorem add_pos_tactic {a b : ℕ} (ha : 0 < a) : 0 < a + b := by
  omega
-- BOOK: end term-vs-tactic

-- BOOK: begin term-show
-- show と from で項スタイルに注釈を入れる
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q :=
  show P ∧ Q from ⟨hp, hq⟩
-- BOOK: end term-show

end Handbook.C05
