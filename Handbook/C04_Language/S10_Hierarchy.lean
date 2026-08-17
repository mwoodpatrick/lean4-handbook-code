/- 第4章 Lean 言語の基礎
   4.6b 型クラスの継承 — mathlib の階層はこう作られている -/
import Mathlib

namespace Handbook.C04

-- BOOK: begin hier-extends
-- extends で既存の型クラスを引き継ぐ
class MyMul (α : Type) where
  mul : α → α → α

class MySemigroup (α : Type) extends MyMul α where
  mul_assoc : ∀ a b c : α,
    MyMul.mul (MyMul.mul a b) c = MyMul.mul a (MyMul.mul b c)
-- BOOK: end hier-extends

-- BOOK: begin hier-instance
-- インスタンスを登録すると、親の能力も自動で使える
instance : MyMul ℕ where
  mul := Nat.mul

instance : MySemigroup ℕ where
  mul_assoc := Nat.mul_assoc

#eval MyMul.mul (3 : ℕ) 4
-- BOOK: end hier-instance

-- BOOK: begin hier-mathlib
-- mathlib の階層も同じ仕組みでできている
#check @Monoid          -- One と Semigroup を束ねたもの
#check @Group           -- Monoid に逆元を足したもの
#check @CommGroup       -- Group に可換性を足したもの

-- 群の定理は、可換群にもそのまま使える
example (G : Type) [CommGroup G] (a : G) : a * a⁻¹ = 1 :=
  mul_inv_cancel a
-- BOOK: end hier-mathlib

-- BOOK: begin hier-diamond
-- 複数の親を持ってもよい。可換モノイドは2方向から来る
#check @CommMonoid

-- ℕ は多くのインスタンスを同時に持つ
example : CommMonoid ℕ := inferInstance
example : AddCommMonoid ℕ := inferInstance
-- BOOK: end hier-diamond

end Handbook.C04
