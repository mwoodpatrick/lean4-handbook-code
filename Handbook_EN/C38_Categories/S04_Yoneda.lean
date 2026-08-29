/- English edition source: Handbook/C38_Categories/S04_Yoneda.lean. -/
import Mathlib

namespace Handbook.C38

open CategoryTheory

-- BOOK: begin yoneda
-- The Yoneda embedding sends an object X to the functor Hom(−, X)
#check @CategoryTheory.yoneda

-- The Yoneda lemma: the natural transformations out of Hom(X, −)
-- correspond to the elements of F.obj X
#check @CategoryTheory.yonedaEquiv
-- BOOK: end yoneda

-- BOOK: begin yoneda-faithful
-- The Yoneda embedding is fully faithful: an object is determined by
-- its relations to the others
#check @CategoryTheory.Yoneda.fullyFaithful

-- Corollary: if the representable functors are isomorphic, so are
-- the objects
noncomputable example (C : Type) [Category C] (X Y : C)
    (h : yoneda.obj X ≅ yoneda.obj Y) : X ≅ Y :=
  yoneda.preimageIso h
-- BOOK: end yoneda-faithful

-- BOOK: begin monoidal
-- A monoidal category is a category equipped with a “product” of
-- objects.
#check @CategoryTheory.MonoidalCategory
-- BOOK: end monoidal

end Handbook.C38
