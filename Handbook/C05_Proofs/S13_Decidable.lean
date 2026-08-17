/- 第5章 証明の基本
   5.11 決定可能性 — Bool と Prop を結ぶ橋 -/
import Mathlib

namespace Handbook.C05

-- BOOK: begin dec-decide
-- 決定可能な命題は計算で確かめられる
example : 3 + 4 = 7 := by decide

example : ¬ (2 = 3) := by decide

-- 判定手続きが登録されているかは inferInstance で確かめる
#check (inferInstance : Decidable (3 < 5))
-- BOOK: end dec-decide

-- BOOK: begin dec-bounded
-- 有界な全称・存在も決定可能になる
example : ∀ n < 5, n * n < 25 := by decide

example : ∃ n < 10, n * n = 49 := by decide
-- BOOK: end dec-bounded

-- BOOK: begin dec-limit
-- 有界を外すと決定できない。証明を書くしかない
example : ∀ n : ℕ, 0 ≤ n := by
  intro n
  exact Nat.zero_le n
-- BOOK: end dec-limit

-- BOOK: begin dec-if
-- Decidable インスタンスは if の分岐にも使われる
def sign (n : ℤ) : ℤ := if n < 0 then -1 else 1

example : sign (-3) = -1 := by decide

-- 命題を Bool へ落とす decide 関数もある
#eval decide (3 < 5)
-- BOOK: end dec-if

end Handbook.C05
