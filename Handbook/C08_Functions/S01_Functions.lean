/- 第8章 関数の基礎
   8.1 関数とは何か — 対応から写像へ -/
import Mathlib

namespace Handbook.C08

-- BOOK: begin fun-def
def f (x : ℚ) : ℚ := 2 * x + 1

#eval f 3  -- 出力: 7

-- 関数の相等は「すべての入力で値が一致すること」(外延性)
example : (fun x : ℚ => x + x) = fun x => 2 * x := by
  funext x
  ring
-- BOOK: end fun-def

-- BOOK: begin fun-ext
-- 展開すると同じ式になる2つの関数は、関数として等しい
example : (fun x : ℚ => (x + 1) ^ 2) =
    (fun x : ℚ => x ^ 2 + 2 * x + 1) := by
  funext x
  ring
-- BOOK: end fun-ext

-- BOOK: begin fun-shift
-- グラフの移動は「入力・出力の前処理・後処理」である
def g0 (x : ℚ) : ℚ := x ^ 2

def gShift (x : ℚ) : ℚ := g0 (x - 2) + 3

#eval gShift 2  -- 出力: 3(頂点 (0,0) が (2,3) へ動いた)
#eval gShift 4  -- 出力: 7(= g0 2 + 3)

-- y 軸対称(偶関数): 入力の符号を変えても値が同じ
example (x : ℚ) : g0 (-x) = g0 x := by
  unfold g0; ring
-- 移動後の最小値: 頂点 (2, 3) が最小点になっている
example (x : ℚ) : 3 ≤ gShift x := by
  unfold gShift g0
  nlinarith [sq_nonneg (x - 2)]
-- BOOK: end fun-shift

-- BOOK: begin fun-parity
-- 偶関数 f(−x) = f(x) と奇関数 f(−x) = −f(x)
example (x : ℚ) : (-x) ^ 2 = x ^ 2 := by ring

example (x : ℚ) : (-x) ^ 3 = -(x ^ 3) := by ring
-- BOOK: end fun-parity

-- BOOK: begin fun-gallery
-- 定義域に注意が要る関数: √ は負の入力に junk value 0 を返す
example : Real.sqrt (-4) = 0 := by
  rw [Real.sqrt_eq_zero']
  norm_num

-- 恒等関数 id: 何もしない関数も立派な関数である
example (x : ℚ) : id x = x := rfl
example : Function.Injective (id : ℚ → ℚ) := fun _ _ h => h
-- BOOK: end fun-gallery

end Handbook.C08
