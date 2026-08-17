/- 第6章 数と式
   6.2 式の展開と因数分解 -/
import Mathlib

namespace Handbook.C06

-- BOOK: begin ring-expand
-- 展開も因数分解も、ring には同じ「環の等式」である
example (x y : ℚ) :
    (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by ring

example (x y : ℚ) :
    (x + y) * (x - y) = x ^ 2 - y ^ 2 := by ring

example (x : ℚ) :
    x ^ 3 - 1 = (x - 1) * (x ^ 2 + x + 1) := by ring
-- BOOK: end ring-expand

-- BOOK: begin ring-identity
-- 有名な恒等式(ブラーマグプタ–フィボナッチ)
example (a b c d : ℚ) :
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) =
      (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 := by ring
-- BOOK: end ring-identity

-- BOOK: begin ring-cube
-- 3乗の和の因数分解
example (x y : ℚ) :
    x ^ 3 + y ^ 3 = (x + y) * (x ^ 2 - x * y + y ^ 2) := by
  ring

-- 平方完成
example (x : ℚ) :
    x ^ 2 - 6 * x + 13 = (x - 3) ^ 2 + 4 := by
  ring
-- BOOK: end ring-cube

-- BOOK: begin ring-mental
-- 暗算術も恒等式である: 99² = (100 − 1)²
example (a b : ℤ) :
    (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by ring

example : (99 : ℤ) ^ 2 = 9801 := by norm_num
-- BOOK: end ring-mental

-- BOOK: begin ring-symmetric
-- 3変数でも同じ。展開の途中経過は ring が全部引き受ける。
example (a b c : ℚ) :
    (a + b + c) ^ 2 =
      a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + b * c + c * a) := by
  ring
-- BOOK: end ring-symmetric

-- BOOK: begin ring-cube3
-- 3乗の展開。係数 1, 3, 3, 1 はパスカルの三角形の第3段。
example (a b : ℚ) :
    (a + b) ^ 3 =
      a ^ 3 + 3 * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3 := by
  ring
-- BOOK: end ring-cube3

-- BOOK: begin ring-sophie
-- ソフィー・ジェルマンの恒等式: a⁴ + 4b⁴ は必ず分解できる
example (a b : ℚ) :
    a ^ 4 + 4 * b ^ 4 =
      ((a + b) ^ 2 + b ^ 2) * ((a - b) ^ 2 + b ^ 2) := by
  ring
-- BOOK: end ring-sophie

end Handbook.C06
