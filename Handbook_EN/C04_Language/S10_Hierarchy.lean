/- English edition source: Handbook/C04_Language/S10_Hierarchy.lean. -/
import Mathlib

namespace Handbook.C04

-- BOOK: begin hier-extends
-- extends inherits from an existing type class
class MyMul (α : Type) where
  mul : α → α → α

class MySemigroup (α : Type) extends MyMul α where
  mul_assoc : ∀ a b c : α,
    MyMul.mul (MyMul.mul a b) c = MyMul.mul a (MyMul.mul b c)
-- BOOK: end hier-extends

-- BOOK: begin hier-instance
-- Once we register an instance, the parent's abilities become usable
-- automatically too
instance : MyMul ℕ where
  mul := Nat.mul

instance : MySemigroup ℕ where
  mul_assoc := Nat.mul_assoc

#eval MyMul.mul (3 : ℕ) 4
-- BOOK: end hier-instance

-- BOOK: begin hier-mathlib
-- mathlib's hierarchy is built by the same mechanism
#check @Monoid          -- One and Semigroup bundled together
#check @Group           -- Monoid with inverses added
#check @CommGroup       -- Group with commutativity added

-- Theorems about groups apply directly to commutative groups too
example (G : Type) [CommGroup G] (a : G) : a * a⁻¹ = 1 :=
  mul_inv_cancel a
-- BOOK: end hier-mathlib

-- BOOK: begin hier-diamond
-- A class may have several parents. A commutative monoid comes from two
-- directions.
#check @CommMonoid

-- ℕ carries many instances simultaneously
example : CommMonoid ℕ := inferInstance
example : AddCommMonoid ℕ := inferInstance
-- BOOK: end hier-diamond

end Handbook.C04
