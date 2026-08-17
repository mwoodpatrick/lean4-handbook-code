/- 第12章 数列と数学的帰納法
   12.4 数学的帰納法の仕組み — 帰納型再訪 -/
import Mathlib

namespace Handbook.C12

-- BOOK: begin ind-anatomy
-- induction タクティクは、ゴールを「n = 0 の場合」と
-- 「n = k + 1 の場合(帰納法の仮定 ih 付き)」に分割する
theorem sum_odds (n : ℕ) :
    ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring
-- BOOK: end ind-anatomy

-- BOOK: begin nat-rec
-- induction の正体は帰納型 Nat が生む再帰子 Nat.rec である。
-- タクティクを使わず、再帰子を直接当てても同じ証明になる。
example (n : ℕ) : 0 + n = n :=
  Nat.rec (motive := fun m => 0 + m = m)
    rfl
    (fun m ih => by rw [Nat.add_succ, ih])
    n
-- BOOK: end nat-rec

-- BOOK: begin ind-two-step
-- 2 ずつ進む帰納法も、道具立ては同じ(Nat.le_induction の親戚)。
-- ここでは偶数の平方が 4 の倍数であることを普通の帰納法で示す。
theorem four_dvd_sq_of_even (n : ℕ) :
    4 ∣ (2 * n) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : (2 * (n + 1)) ^ 2 = (2 * n) ^ 2 + 4 * (2 * n + 1) := by
      ring
    rw [h]
    omega
-- BOOK: end ind-two-step

end Handbook.C12
