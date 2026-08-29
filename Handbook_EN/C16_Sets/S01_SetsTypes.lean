/- English edition source: Handbook/C16_Sets/S01_SetsTypes.lean. -/
import Mathlib

namespace Handbook.C16

-- BOOK: begin set-def
-- Set α is really “a predicate on α” (Set α := α → Prop)
def evens : Set ℕ := {n | n % 2 = 0}

-- Membership x ∈ S means that the predicate S x holds
example : 4 ∈ evens := rfl

example : 7 ∉ evens := by simp [evens]
-- BOOK: end set-def

-- BOOK: begin set-vs-type
-- A type is a “universe”; a set is a “region within that universe”
#check ℕ            -- a type
#check evens        -- Set ℕ (a region inside the universe ℕ)
#check {n : ℕ | n % 2 = 0}  -- set-builder notation
-- BOOK: end set-vs-type

-- BOOK: begin set-subset
-- Subset ⊆ is exactly an implication of membership
example : evens ⊆ {n : ℕ | n % 2 = 0} := fun _ h => h

-- Membership in a set-builder set unfolds to the predicate itself
-- (closed by Iff.rfl)
example (n : ℕ) : n ∈ {m : ℕ | m % 2 = 0} ↔ n % 2 = 0 := Iff.rfl
-- BOOK: end set-subset

end Handbook.C16
