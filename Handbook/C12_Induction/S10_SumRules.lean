/- 第12章 数列と数学的帰納法
   12.4b 総和の操作規則 -/
import Mathlib

namespace Handbook.C12

-- BOOK: begin rule-linear
-- 総和は線形。和は分けられ、定数倍は外へ出せる
example (n : ℕ) (f g : ℕ → ℚ) :
    ∑ i ∈ Finset.range n, (f i + g i)
      = (∑ i ∈ Finset.range n, f i)
        + ∑ i ∈ Finset.range n, g i :=
  Finset.sum_add_distrib

example (n : ℕ) (c : ℚ) (f : ℕ → ℚ) :
    ∑ i ∈ Finset.range n, c * f i
      = c * ∑ i ∈ Finset.range n, f i :=
  (Finset.mul_sum _ _ _).symm
-- BOOK: end rule-linear

-- BOOK: begin rule-const
-- 定数の和は個数倍
example (n : ℕ) (c : ℚ) :
    ∑ _i ∈ Finset.range n, c = n * c := by
  simp [Finset.sum_const, nsmul_eq_mul]
-- BOOK: end rule-const

-- BOOK: begin rule-swap
-- 二重和は順序を入れ替えられる(有限だから条件なしで成り立つ)
example (m n : ℕ) (f : ℕ → ℕ → ℚ) :
    ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, f i j
      = ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range m, f i j :=
  Finset.sum_comm
-- BOOK: end rule-swap

-- BOOK: begin rule-prod
-- 総乗も同じ枠組み。加法を乗法に替えただけである
example : ∏ i ∈ Finset.range 4, (i + 1) = 24 := by decide

example (n : ℕ) : ∏ _i ∈ Finset.range n, (1 : ℚ) = 1 := by
  simp
-- BOOK: end rule-prod

end Handbook.C12
