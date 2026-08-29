/- Chapter 39: Introduction to algebraic geometry
   39.5 Sheaves and schemes -/
import Mathlib

namespace Handbook.C39

-- BOOK: begin sheaf
-- A sheaf is a contravariant functor from the category of open sets
-- to the category of rings (Chapter 38)
#check @TopologicalSpace.Opens
-- BOOK: end sheaf

-- BOOK: begin localization
-- Localization: the ring in which f is made invertible.
-- This is the ring the structure sheaf puts on D(f).
#check @Localization.Away
-- localizing ℤ at 2 gives ℤ[1/2], the rationals whose denominators
-- are powers of 2
example : CommRing (Localization.Away (2 : ℤ)) := by
  infer_instance
-- BOOK: end localization

-- BOOK: begin scheme
-- Schemes: the basic notion of modern algebraic geometry,
-- completely formalized
#check @AlgebraicGeometry.Scheme
-- the Spec functor: an affine scheme out of a commutative ring
#check @AlgebraicGeometry.Spec
-- BOOK: end scheme

end Handbook.C39
