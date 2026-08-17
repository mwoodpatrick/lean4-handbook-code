/- 第24章 多変数の微積分
   24.5 勾配 — 全微分をベクトルに直す -/
import Mathlib

namespace Handbook.C24

-- BOOK: begin gradient-def
-- 勾配は内積空間でのみ定義される(内積が要る)
#check @gradient

-- 勾配の定義そのもの: HasGradientAt f g x とは
-- 全微分が「g との内積をとる線形写像」であること
example {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] (f : F → ℝ) (g x : F) :
    HasGradientAt f g x ↔
      HasFDerivAt f (InnerProductSpace.toDual ℝ F g) x :=
  hasGradientAt_iff_hasFDerivAt
-- BOOK: end gradient-def

-- BOOK: begin gradient-line
-- 1 次元では勾配はただの微分係数に戻る
#check @gradient_eq_deriv
-- BOOK: end gradient-line

end Handbook.C24
