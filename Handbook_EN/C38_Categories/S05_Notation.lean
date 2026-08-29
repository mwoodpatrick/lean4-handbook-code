/- English edition source: Handbook/C38_Categories/S05_Notation.lean. -/
import Mathlib

namespace Handbook.C38

open CategoryTheory

-- BOOK: begin nota-arrows
-- An arrow is written ⟶ and composition ≫
example {C : Type} [Category C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) : X ⟶ Z := f ≫ g

-- the identity and associativity laws are handled by simp
example {C : Type} [Category C] {X Y : C} (f : X ⟶ Y) :
    𝟙 X ≫ f = f := by simp
-- BOOK: end nota-arrows

-- BOOK: begin nota-functor
-- A functor is written ⥤ (typed \func)
example {C D : Type} [Category C] [Category D]
    (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) : F.obj X ⟶ F.obj Y :=
  F.map f

-- a functor preserves composition; this is part of the definition
example {C D : Type} [Category C] [Category D] (F : C ⥤ D)
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map (f ≫ g) = F.map f ≫ F.map g := by simp
-- BOOK: end nota-functor

-- BOOK: begin nota-nat
-- A natural transformation is applied at an object with .app X
example {C D : Type} [Category C] [Category D]
    {F G : C ⥤ D} (α : F ⟶ G) (X : C) : F.obj X ⟶ G.obj X :=
  α.app X

-- the naturality square commutes
example {C D : Type} [Category C] [Category D]
    {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (f : X ⟶ Y) :
    F.map f ≫ α.app Y = α.app X ≫ G.map f := α.naturality f
-- BOOK: end nota-nat

-- BOOK: begin nota-iso
-- An isomorphism carries .hom and .inv, going each way
example {C : Type} [Category C] {X Y : C} (e : X ≅ Y) :
    e.hom ≫ e.inv = 𝟙 X := e.hom_inv_id
-- BOOK: end nota-iso

end Handbook.C38
