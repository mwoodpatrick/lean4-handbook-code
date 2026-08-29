/- English edition source: Handbook/C38_Categories/S03_Adjunction.lean. -/
import Mathlib

namespace Handbook.C38

open CategoryTheory

-- BOOK: begin adjunction
-- An adjunction F ⊣ G: Hom(F X, Y) and Hom(X, G Y) correspond
-- naturally
#check @CategoryTheory.Adjunction

-- the correspondence is a bijection, usable in either direction
example (C D : Type) [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G) (X : C) (Y : D) :
    (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y) :=
  adj.homEquiv X Y
-- BOOK: end adjunction

-- BOOK: begin free-forgetful
-- The typical example: a free construction is left adjoint to a
-- forgetful functor
#check @CategoryTheory.Adjunction.mkOfHomEquiv

-- The unit and counit give another way of stating an adjunction
example (C D : Type) [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G) :
    Functor.id C ⟶ F ⋙ G :=
  adj.unit
-- BOOK: end free-forgetful

end Handbook.C38
