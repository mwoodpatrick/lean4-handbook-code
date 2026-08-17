/- 第38章 圏論
   38.1 圏・関手・自然変換 / 38.2 mathlib の記法 -/
import Mathlib

namespace Handbook.C38

open CategoryTheory

-- BOOK: begin category-axioms
-- 圏の構成要素: 恒等射 𝟙 と合成 ≫
example (C : Type) [Category C] (X : C) : X ⟶ X := 𝟙 X

example (C : Type) [Category C] (X Y Z : C)
    (f : X ⟶ Y) (g : Y ⟶ Z) : X ⟶ Z := f ≫ g

-- 圏の公理: 単位律と結合律
example (C : Type) [Category C] (X Y : C) (f : X ⟶ Y) :
    𝟙 X ≫ f = f :=
  Category.id_comp f

example (C : Type) [Category C] (W X Y Z : C)
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f ≫ g) ≫ h = f ≫ (g ≫ h) :=
  Category.assoc f g h
-- BOOK: end category-axioms

-- BOOK: begin functor
-- 関手 C ⥤ D: 対象と射の両方を写し、合成と恒等を保つ
#check @CategoryTheory.Functor

-- 恒等関手と関手の合成
example (C : Type) [Category C] : C ⥤ C := Functor.id C

example (C D E : Type) [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) : C ⥤ E := F ⋙ G
-- BOOK: end functor

-- BOOK: begin nat-trans
-- 自然変換: 関手の間の射。各対象で射を与え、四角形が可換
#check @CategoryTheory.NatTrans

-- 同型 ≅ は「逆を持つ射」
example (C : Type) [Category C] (X Y : C) (e : X ≅ Y) :
    e.hom ≫ e.inv = 𝟙 X :=
  e.hom_inv_id
-- BOOK: end nat-trans

end Handbook.C38
