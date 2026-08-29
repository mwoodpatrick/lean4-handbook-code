/- English edition source: Handbook/C04_Language/S09_Binders.lean. -/
import Mathlib

namespace Handbook.C04

-- BOOK: begin bind-explicit
-- () is an explicit argument. The caller must always write it.
def pairUp (α : Type) (a b : α) : α × α := (a, b)

#check pairUp ℕ 1 2
-- BOOK: end bind-explicit

-- BOOK: begin bind-implicit
-- {} is an implicit argument. Lean infers it from the types of the
-- other arguments.
def pairUp' {α : Type} (a b : α) : α × α := (a, b)

#check pairUp' 1 2        -- α is inferred to be ℕ
#check @pairUp' ℕ 1 2     -- with @ we can pass it explicitly
-- BOOK: end bind-implicit

-- BOOK: begin bind-inst
-- [] is an instance argument. It is filled in by type-class search.
def sumPair {α : Type} [Add α] (p : α × α) : α := p.1 + p.2

#eval sumPair (3, 4)
-- BOOK: end bind-inst

-- BOOK: begin bind-variable
-- variable declares, all at once, "arguments shared by the declarations
-- below"
section
variable {G : Type} [Group G]

-- both of the two below implicitly receive {G} [Group G]
theorem inv_inv_self (g : G) : g⁻¹⁻¹ = g := inv_inv g

theorem mul_inv_self (g : G) : g * g⁻¹ = 1 := mul_inv_cancel g

end
-- BOOK: end bind-variable

-- BOOK: begin bind-strict
-- ⦃⦄ is strict implicit. It stays unfilled until an explicit argument
-- follows.
example {α : Type} (f : α → α) (a : α) : α := f a
-- BOOK: end bind-strict

end Handbook.C04
