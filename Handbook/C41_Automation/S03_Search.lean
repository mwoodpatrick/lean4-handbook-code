/- 第41章 証明自動化
   41.4 探索型 -/
import Mathlib

namespace Handbook.C41

-- BOOK: begin aesop
-- aesop: ルールベースの証明探索。論理と集合の定型処理に強い
example (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) (hp : P) :
    R ∧ P := by
  aesop

example (s t : Set ℕ) (x : ℕ) (h : x ∈ s) : x ∈ s ∪ t := by
  aesop
-- BOOK: end aesop

-- BOOK: begin aesop-limit
-- aesop も万能ではない。算術は苦手なので専用 tactic に任せる
example (a b : ℤ) (h : a ≤ b) : a - 1 < b := by
  omega

-- 環の等式は ring が確実
example (x y : ℚ) : (x + y) ^ 2 - (x - y) ^ 2 = 4 * (x * y) := by
  ring
-- BOOK: end aesop-limit

end Handbook.C41
