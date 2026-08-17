/- 第4章 Lean 言語の基礎
   4.6 構造体と型クラス -/
import Mathlib

namespace Handbook.C04

-- BOOK: begin struct-point
-- 構造体はフィールドの束
structure Point where
  x : ℚ
  y : ℚ
  deriving Repr

def p : Point := ⟨1, 2⟩

#eval p.x + p.y  -- 出力: 3
-- BOOK: end struct-point

-- BOOK: begin struct-class
-- 型クラス: 「大きさが測れる」という能力を型に付与する
class HasSize (α : Type) where
  size : α → ℚ

instance : HasSize Point where
  size q := |q.x| + |q.y|

#eval HasSize.size p  -- 出力: 3
-- BOOK: end struct-class

-- BOOK: begin struct-update
-- with 構文: 一部のフィールドだけ変えた新しい値を作る
def q : Point := { p with y := 5 }

#eval q  -- 出力: { x := 1, y := 5 }
#eval p  -- 出力: { x := 1, y := 2 }(元の p は変わらない)
-- BOOK: end struct-update

end Handbook.C04
