/- 第7章 方程式と不等式
   7.1b 3次方程式 — 解の公式はあるが使わない -/
import Mathlib

namespace Handbook.C07

-- BOOK: begin cubic-depressed
-- 3次方程式は x = y - b/(3a) で2次の項を消せる(チルンハウス変換)
example (b y : ℝ) :
    (y - b / 3) ^ 3 + b * (y - b / 3) ^ 2
      = y ^ 3 - (b ^ 2 / 3) * y + 2 * b ^ 3 / 27 := by
  ring
-- BOOK: end cubic-depressed

-- BOOK: begin cubic-cardano
-- カルダノの公式の核。u + v が y³ + py + q = 0 の解になる条件は
-- u³ + v³ = -q かつ 3uv = -p である
example (u v p q : ℝ) (h1 : u ^ 3 + v ^ 3 = -q)
    (h2 : 3 * u * v = -p) :
    (u + v) ^ 3 + p * (u + v) + q = 0 := by
  have hp : p = -(3 * u * v) := by linarith
  subst hp
  nlinarith [h1]
-- BOOK: end cubic-cardano

-- BOOK: begin cubic-rational
-- 実務では有理根定理で当たりを付けるほうが速い
example (x : ℝ) (h : x ^ 3 - 6 * x ^ 2 + 11 * x - 6 = 0) :
    x = 1 ∨ x = 2 ∨ x = 3 := by
  have : (x - 1) * (x - 2) * (x - 3) = 0 := by linarith [h];
  rcases mul_eq_zero.mp this with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · left; linarith
    · right; left; linarith
  · right; right; linarith
-- BOOK: end cubic-rational

end Handbook.C07
