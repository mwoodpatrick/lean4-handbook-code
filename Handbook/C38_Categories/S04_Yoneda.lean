/- 第38章 圏論
   38.5 米田の補題 / 38.6 モノイダル圏 -/
import Mathlib

namespace Handbook.C38

open CategoryTheory

-- BOOK: begin yoneda
-- 米田埋め込み: 対象 X を「X への射の集まり」に対応させる関手
#check @CategoryTheory.yoneda

-- 米田の補題。自然変換の集まりが F.obj X と一致する
#check @CategoryTheory.yonedaEquiv
-- BOOK: end yoneda

-- BOOK: begin yoneda-faithful
-- 米田埋め込みは充満忠実。対象は「他との関係」で決まる
#check @CategoryTheory.Yoneda.fullyFaithful

-- 系: 表現可能関手が同型なら対象も同型
noncomputable example (C : Type) [Category C] (X Y : C)
    (h : yoneda.obj X ≅ yoneda.obj Y) : X ≅ Y :=
  yoneda.preimageIso h
-- BOOK: end yoneda-faithful

-- BOOK: begin monoidal
-- モノイダル圏: 対象どうしの「積」を持つ圏
#check @CategoryTheory.MonoidalCategory
-- BOOK: end monoidal

end Handbook.C38
