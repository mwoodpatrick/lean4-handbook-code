/- English edition source: Handbook/C38_Categories/S01_Category.lean. -/
import Mathlib

namespace Handbook.C38

open CategoryTheory

-- BOOK: begin category-axioms
-- The components of a category are identity morphisms 𝟙 and composition
-- ≫.
example (C : Type) [Category C] (X : C) : X ⟶ X := 𝟙 X

example (C : Type) [Category C] (X Y Z : C)
    (f : X ⟶ Y) (g : Y ⟶ Z) : X ⟶ Z := f ≫ g

-- The axioms of a category: identity and associativity
example (C : Type) [Category C] (X Y : C) (f : X ⟶ Y) :
    𝟙 X ≫ f = f :=
  Category.id_comp f

example (C : Type) [Category C] (W X Y Z : C)
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f ≫ g) ≫ h = f ≫ (g ≫ h) :=
  Category.assoc f g h
-- BOOK: end category-axioms

-- BOOK: begin functor
-- A functor C ⥤ D maps both objects and arrows, preserving
-- composition and identities
#check @CategoryTheory.Functor

-- The identity functor and composition of functors.
example (C : Type) [Category C] : C ⥤ C := Functor.id C

example (C D E : Type) [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) : C ⥤ E := F ⋙ G
-- BOOK: end functor

-- BOOK: begin nat-trans
-- A natural transformation: an arrow between functors, given by an
-- arrow at each object making the squares commute
#check @CategoryTheory.NatTrans

-- an isomorphism is an arrow with a two-sided inverse
example (C : Type) [Category C] (X Y : C) (e : X ≅ Y) :
    e.hom ≫ e.inv = 𝟙 X :=
  e.hom_inv_id
-- BOOK: end nat-trans

end Handbook.C38
