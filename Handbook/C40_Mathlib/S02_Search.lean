/- 第40章 mathlib の歩き方
   40.3 検索術 -/
import Mathlib

namespace Handbook.C40

-- BOOK: begin search-exact
-- exact? は現在のゴールをそのまま閉じる補題を探す
example (a b : ℕ) (h : a ≤ b) : a ≤ b + 1 := by
  exact?
-- BOOK: end search-exact

-- BOOK: begin search-apply
-- exact? が見つけた項をそのまま書けば、以後は探索なしで通る
example (a b : ℕ) (h : a ≤ b) : a ≤ b + 1 :=
  Nat.le_succ_of_le h

-- 仮定から出るなら assumption、simp 補題で閉じるなら simp
example (a b : ℕ) (h : a ≤ b) : a ≤ b := by assumption
example (a : ℕ) : a ∈ {x : ℕ | x = a} := by simp
-- BOOK: end search-apply

-- BOOK: begin search-check
-- #check で型を確かめ、名前の当たりを付ける
#check @Nat.le_succ_of_le
#check @Nat.succ_le_of_lt
#check @Nat.lt_succ_iff
-- BOOK: end search-check

end Handbook.C40
