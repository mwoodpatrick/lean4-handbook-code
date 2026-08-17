/- 第40章 mathlib の歩き方
   40.6 mathlib の設計哲学 -/
import Mathlib

namespace Handbook.C40

-- BOOK: begin design-general
-- 一般性の利得: add_comm は可換モノイドすべてに効く
#check @add_comm

-- ℕ でも ℝ でも行列でも、同じ1本の定理を使う
example (a b : ℕ) : a + b = b + a := add_comm a b
example (a b : ℝ) : a + b = b + a := add_comm a b
example (a b : Polynomial ℤ) : a + b = b + a := add_comm a b
-- BOOK: end design-general

-- BOOK: begin design-cost
-- 一般性の代償: 名前から具体的な型が消え、検索しづらくなる
-- ℕ 専用の名前も残されているが、内容は一般版と同じ
#check @Nat.add_comm
#check @add_comm

-- 一般版で書くと、後から型を変えても証明が動く
example (R : Type) [AddCommMonoid R] (a b c : R) :
    a + b + c = c + (b + a) := by
  rw [add_comm a b, add_comm (b + a) c]
-- BOOK: end design-cost

end Handbook.C40
