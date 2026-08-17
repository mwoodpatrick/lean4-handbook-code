/- 第3章 環境構築
   3.1 ブラウザで始める — Playground に貼り付ける最初のコード -/
import Mathlib

namespace Handbook.C03

-- BOOK: begin first-proof
-- 環境が動いていれば、この2行に緑のチェックが付く
theorem my_first_proof : 2 + 2 = 4 := rfl

#eval "Lean is running!"  -- 出力: "Lean is running!"
-- BOOK: end first-proof

-- BOOK: begin check-mathlib
-- mathlib が読み込めているかの確認。
-- 素数判定が通れば、標準ライブラリだけでなく mathlib も動いている
example : Nat.Prime 97 := by norm_num

-- 実数と極限が使えるか(mathlib の解析パートの確認)
#check @Real.sqrt
#check @Filter.Tendsto
-- BOOK: end check-mathlib

-- BOOK: begin first-tactic
-- タクティクで書く最初の証明。
-- intro で仮定を取り込み、exact で目標に当てる
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp
  · exact hq
-- BOOK: end first-tactic

end Handbook.C03
