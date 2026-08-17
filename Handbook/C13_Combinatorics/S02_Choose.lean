/- 第13章 場合の数と確率
   13.2 順列と組合せ -/
import Mathlib

namespace Handbook.C13

open scoped Nat

-- BOOK: begin choose-eval
#eval Nat.factorial 5        -- 出力: 120(5個の並べ方)
#eval Nat.descFactorial 5 2  -- 出力: 20(5個から2個並べる ₅P₂)
#eval Nat.choose 5 2         -- 出力: 10(5個から2個選ぶ ₅C₂)
-- BOOK: end choose-eval

-- BOOK: begin choose-formula
-- 教科書の公式 C(n,k) = n! / (k!(n-k)!)
example (n k : ℕ) (h : k ≤ n) :
    Nat.choose n k = n ! / (k ! * (n - k)!) :=
  Nat.choose_eq_factorial_div_factorial h

-- パスカルの法則(パスカルの三角形の漸化式)
example (n k : ℕ) :
    Nat.choose (n + 1) (k + 1)
      = Nat.choose n k + Nat.choose n (k + 1) :=
  Nat.choose_succ_succ n k
-- BOOK: end choose-formula

-- BOOK: begin choose-symm
-- 対称性 C(n,k) = C(n,n−k):「選ぶ」=「残す」
example (n k : ℕ) (h : k ≤ n) :
    Nat.choose n k = Nat.choose n (n - k) :=
  (Nat.choose_symm h).symm

#eval Nat.choose 10 7  -- 出力: 120(= C(10,3))
-- BOOK: end choose-symm

-- BOOK: begin choose-card
-- 「k 元部分集合の個数が C(n,k)」という数え上げの本体
example (n k : ℕ) :
    ((Finset.range n).powersetCard k).card = Nat.choose n k := by
  simp
-- BOOK: end choose-card

-- BOOK: begin perm-enum
-- 並べ方は列挙できる。3! = 6 通りの全リスト。
#eval [1, 2, 3].permutations
-- 出力: [[1,2,3], [2,1,3], [3,2,1], [2,3,1], [3,1,2], [1,3,2]]

example : [1, 2, 3].permutations.length = Nat.factorial 3 := by
  rw [List.length_permutations]
  decide
-- BOOK: end perm-enum

-- BOOK: begin choose-handshake
-- 30人が全員と1回ずつ握手すると C(30,2) = 30·29/2 = 435 回
example : Nat.choose 30 2 = 435 := by
  rw [Nat.choose_two_right]

-- 一般式 C(n,2) = n(n−1)/2 は名前付きの定理
example (n : ℕ) : Nat.choose n 2 = n * (n - 1) / 2 :=
  Nat.choose_two_right n
-- BOOK: end choose-handshake

-- BOOK: begin choose-lattice
-- 格子路: 右へ4・上へ3 の最短経路は「7歩中どの3歩を上にするか」
example : Nat.choose 7 3 = 35 := by decide

#eval Nat.choose 7 3  -- 出力: 35
-- BOOK: end choose-lattice

-- BOOK: begin choose-multiset
-- 同じものを含む順列: MISSISSIPPI(I×4, S×4, P×2)の並べ方
#eval Nat.factorial 11 /
  (Nat.factorial 4 * Nat.factorial 4 * Nat.factorial 2)
-- 出力: 34650

example :
    Nat.factorial 11 /
      (Nat.factorial 4 * Nat.factorial 4 * Nat.factorial 2)
      = 34650 := by
  decide
-- BOOK: end choose-multiset

end Handbook.C13
