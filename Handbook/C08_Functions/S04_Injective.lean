/- 第8章 関数の基礎
   8.4 単射・全射・逆関数 -/
import Mathlib

namespace Handbook.C08

-- BOOK: begin inj-def
-- 単射: 値が同じなら入力も同じ
example : Function.Injective (fun x : ℚ => 2 * x + 1) := by
  intro a b h
  dsimp only at h
  linarith
-- BOOK: end inj-def

-- BOOK: begin surj-def
-- 全射: どの値にも逆像がある。証拠は逆関数の式そのもの。
example : Function.Surjective (fun x : ℚ => 2 * x + 1) := by
  intro y
  use (y - 1) / 2
  dsimp only
  ring
-- BOOK: end surj-def

-- BOOK: begin inj-counter
-- x² は単射でない: 1 と -1 が同じ値 1 に行く
example : ¬ Function.Injective (fun x : ℤ => x ^ 2) := by
  intro h
  have : (1 : ℤ) = -1 := h (by norm_num)
  norm_num at this
-- BOOK: end inj-counter

-- BOOK: begin bij-def
-- 全単射 = 単射 かつ 全射
example : Function.Bijective (fun x : ℚ => 2 * x + 1) :=
  ⟨fun a b h => by dsimp only at h; linarith,
   fun y => ⟨(y - 1) / 2, by dsimp only; ring⟩⟩
-- BOOK: end bij-def

-- BOOK: begin fun-count
-- 有限集合の間の関数は数えられる: 3元→2元 の関数は 2³ = 8 個
example : (Finset.univ : Finset (Fin 3 → Fin 2)).card = 8 := by
  decide

-- 2元→3元 の単射は 3 × 2 = 6 個(順列 ₃P₂)
example :
    ((Finset.univ : Finset (Fin 2 → Fin 3)).filter
      Function.Injective).card = 6 := by
  decide
-- BOOK: end fun-count

-- BOOK: begin equiv
-- 逆関数まで込みのデータが Equiv(≃): 往復の関数と往復の証明
def double : ℚ ≃ ℚ where
  toFun x := 2 * x + 1
  invFun y := (y - 1) / 2
  left_inv x := by dsimp; ring
  right_inv y := by dsimp; ring

#eval double 3        -- 出力: 7
#eval double.symm 7   -- 出力: 3(逆向きに使う)
-- BOOK: end equiv

end Handbook.C08
