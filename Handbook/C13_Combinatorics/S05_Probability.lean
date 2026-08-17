/- 第13章 場合の数と確率
   13.6 古典的確率 — Finset.card の比として -/
import Mathlib

namespace Handbook.C13

-- BOOK: begin dice
-- 2個のさいころ(目は 0..5 で持ち、実際の目は +1 と読む)
def dice : Finset (ℕ × ℕ) :=
  (Finset.range 6) ×ˢ (Finset.range 6)

-- 目の和が 7(0 起点では 5)になる出方
def sum7 : Finset (ℕ × ℕ) :=
  dice.filter (fun p => p.1 + p.2 = 5)

#eval dice.card  -- 出力: 36
#eval sum7.card  -- 出力: 6
-- BOOK: end dice

-- BOOK: begin dice-prob
-- 古典的確率 = 場合の数の比。和が 7 になる確率は 1/6。
example : (sum7.card : ℚ) / dice.card = 1 / 6 := by
  have h1 : sum7.card = 6 := by decide
  have h2 : dice.card = 36 := by decide
  rw [h1, h2]
  norm_num
-- BOOK: end dice-prob

-- BOOK: begin dice-atleast
-- 「少なくとも1つが 6」は余事象で数える: 36 − 25 = 11
def hasSix : Finset (ℕ × ℕ) :=
  dice.filter (fun p => p.1 = 5 ∨ p.2 = 5)

example : hasSix.card = 11 := by decide

example : (hasSix.card : ℚ) / dice.card = 11 / 36 := by
  have h : hasSix.card = 11 := by decide
  have h2 : dice.card = 36 := by decide
  rw [h, h2]
  norm_num
-- BOOK: end dice-atleast

-- BOOK: begin expectation
-- さいころの目の平均(期待値): (1+2+…+6)/6 = 7/2
#eval ((Finset.range 6).sum (fun k => (k + 1 : ℚ))) / 6
-- 出力: 7/2

example :
    ((Finset.range 6).sum (fun k => (k + 1 : ℚ))) / 6
      = 7 / 2 := by
  norm_num [Finset.sum_range_succ]
-- BOOK: end expectation

-- BOOK: begin binom-prob
-- 反復試行: コイン5回で表がちょうど3回の確率は C(5,3)/2⁵
example : (Nat.choose 5 3 : ℚ) / 2 ^ 5 = 5 / 16 := by
  have h : Nat.choose 5 3 = 10 := by decide
  rw [h]
  norm_num
-- BOOK: end binom-prob

-- BOOK: begin comb-exercises
-- 演習: 二項係数・階乗・境界値
example : Nat.choose 6 3 = 20 := by decide

example : Nat.factorial 6 = 720 := by decide

example (n : ℕ) : Nat.choose n 0 = 1 := Nat.choose_zero_right n
-- BOOK: end comb-exercises

end Handbook.C13
