/- 第38章 圏論
   38.2 mathlib の圏論ライブラリの記法 -/
import Mathlib

namespace Handbook.C38

open CategoryTheory

-- BOOK: begin nota-arrows
-- 射は ⟶(\hom)、合成は ≫(\gg)で左から右へ書く
example {C : Type} [Category C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) : X ⟶ Z := f ≫ g

-- 恒等射は 𝟙。単位律と結合律は simp で処理される
example {C : Type} [Category C] {X Y : C} (f : X ⟶ Y) :
    𝟙 X ≫ f = f := by simp
-- BOOK: end nota-arrows

-- BOOK: begin nota-functor
-- 関手は ⥤(\func)、関手の合成は ⋙
example {C D : Type} [Category C] [Category D]
    (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) : F.obj X ⟶ F.obj Y :=
  F.map f

-- 関手は合成を保つ。これが定義の一部である
example {C D : Type} [Category C] [Category D] (F : C ⥤ D)
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map (f ≫ g) = F.map f ≫ F.map g := by simp
-- BOOK: end nota-functor

-- BOOK: begin nota-nat
-- 自然変換は ⟹。成分は .app X で取り出す
example {C D : Type} [Category C] [Category D]
    {F G : C ⥤ D} (α : F ⟶ G) (X : C) : F.obj X ⟶ G.obj X :=
  α.app X

-- 自然性の四角形が可換であること
example {C D : Type} [Category C] [Category D]
    {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (f : X ⟶ Y) :
    F.map f ≫ α.app Y = α.app X ≫ G.map f := α.naturality f
-- BOOK: end nota-nat

-- BOOK: begin nota-iso
-- 同型は ≅。往路 .hom と復路 .inv を持つ
example {C : Type} [Category C] {X Y : C} (e : X ≅ Y) :
    e.hom ≫ e.inv = 𝟙 X := e.hom_inv_id
-- BOOK: end nota-iso

end Handbook.C38
