/- English edition source: Handbook/C38_Categories/S02_Limits.lean. -/
import Mathlib

namespace Handbook.C38

open CategoryTheory Limits

-- BOOK: begin terminal
-- A terminal object: exactly one arrow comes to it from every object
#check @CategoryTheory.Limits.HasTerminal

-- the one-element type PUnit is terminal in the category of types
example (X : Type) (f g : X → PUnit) : f = g := by
  funext x
  exact Subsingleton.elim _ _
-- BOOK: end terminal

-- BOOK: begin product
-- The universal property of a product: an arrow into the product is
-- determined uniquely
#check @CategoryTheory.Limits.HasBinaryProduct

-- In the category of types, the Cartesian product is the categorical
-- product; projections and pairing satisfy the universal property.
example (X Y Z : Type) (f : Z → X) (g : Z → Y) :
    ∃! h : Z → X × Y, (fun z => (h z).1) = f
      ∧ (fun z => (h z).2) = g := by
  refine ⟨fun z => (f z, g z), ⟨rfl, rfl⟩, ?_⟩
  rintro h ⟨rfl, rfl⟩
  rfl
-- BOOK: end product

-- BOOK: begin limit
-- A limit: the best cone over a diagram, unifying products,
-- equalizers, and pullbacks
#check @CategoryTheory.Limits.HasLimit

-- the colimit is the dual notion (reverse every arrow)
#check @CategoryTheory.Limits.HasColimit
-- BOOK: end limit

end Handbook.C38
