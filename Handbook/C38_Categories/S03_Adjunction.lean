/- 第38章 圏論
   38.4 随伴 -/
import Mathlib

namespace Handbook.C38

open CategoryTheory

-- BOOK: begin adjunction
-- 随伴 F ⊣ G: Hom(F X, Y) と Hom(X, G Y) が自然に対応する
#check @CategoryTheory.Adjunction

-- 随伴から得られる対応。左辺と右辺を行き来できる
example (C D : Type) [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G) (X : C) (Y : D) :
    (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y) :=
  adj.homEquiv X Y
-- BOOK: end adjunction

-- BOOK: begin free-forgetful
-- 典型例: 自由構成と忘却関手が随伴になる
#check @CategoryTheory.Adjunction.mkOfHomEquiv

-- 単位と余単位。随伴の別の表し方
example (C D : Type) [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G) :
    Functor.id C ⟶ F ⋙ G :=
  adj.unit
-- BOOK: end free-forgetful

end Handbook.C38
