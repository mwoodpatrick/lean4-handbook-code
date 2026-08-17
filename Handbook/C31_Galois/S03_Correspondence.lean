/- 第31章 体論とガロア理論
   31.5 ガロア対応 -/
import Mathlib

namespace Handbook.C31

-- BOOK: begin galois-tfae
-- ガロア拡大の同値な特徴づけ。固定体・自己同型の個数・
-- 分解体であること——見た目の違う条件が一致する
#check @IsGalois.tfae
-- BOOK: end galois-tfae

-- BOOK: begin galois-card
-- ガロア拡大では、自己同型の個数がちょうど拡大次数に等しい
example (F E : Type) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] :
    Nat.card (E ≃ₐ[F] E) = Module.finrank F E :=
  IsGalois.card_aut_eq_finrank F E
-- BOOK: end galois-card

-- BOOK: begin fixed-field
-- 部分群が固定する元全体は中間体になる
#check @IntermediateField.fixedField

-- 中間体を固定する自己同型全体は部分群になる
#check @IntermediateField.fixingSubgroup
-- BOOK: end fixed-field

end Handbook.C31
