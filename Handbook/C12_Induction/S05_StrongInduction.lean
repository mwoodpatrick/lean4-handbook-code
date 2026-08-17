/- 第12章 数列と数学的帰納法
   12.5 強帰納法・完全帰納法 -/
import Mathlib

namespace Handbook.C12

-- BOOK: begin strong-ind
-- 2 以上の自然数は素因数を持つ。
-- 「n 未満のすべてで成り立つ」を仮定に使う強帰納法の典型例。
theorem exists_prime_factor :
    ∀ n : ℕ, 2 ≤ n → ∃ p, p.Prime ∧ p ∣ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h2
    by_cases hp : n.Prime
    · exact ⟨n, hp, dvd_refl n⟩
    · -- 素数でなければ真の約数 m(2 ≤ m < n)が取れる
      obtain ⟨m, hdvd, hm2, hmn⟩ :=
        Nat.exists_dvd_of_not_prime2 h2 hp
      obtain ⟨p, hp, hpm⟩ := ih m hmn hm2
      exact ⟨p, hp, hpm.trans hdvd⟩
-- BOOK: end strong-ind

-- BOOK: begin binary-rep
-- 強帰納法のもう一つの顔: 割って小さくする再帰。
-- 正の自然数は 2 進表示の桁数だけ 2 で割れば 0 になる。
def binLength : ℕ → ℕ
  | 0 => 0
  | n + 1 => binLength ((n + 1) / 2) + 1
decreasing_by
  exact Nat.div_lt_self (Nat.succ_pos n) one_lt_two

#eval binLength 6   -- 出力: 3(110₂)
#eval binLength 16  -- 出力: 5(10000₂)
-- BOOK: end binary-rep

-- BOOK: begin le-induction
-- 途中から始める帰納法: n ≥ 4 の範囲で n² ≤ 2ⁿ
theorem sq_le_two_pow {n : ℕ} (hn : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h1 : (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
    calc (n + 1) ^ 2 ≤ 2 * n ^ 2 := h1
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (n + 1) := by rw [pow_succ]; ring
-- BOOK: end le-induction

end Handbook.C12
