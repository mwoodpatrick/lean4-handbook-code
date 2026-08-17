/- 第6章 数と式
   6.3 平方根 — 2の平方根の無理性の完全証明 -/
import Mathlib

namespace Handbook.C06

-- BOOK: begin sqrt2-even
-- 補題: p² が偶数なら p も偶数(2 は素数だから)
theorem two_dvd_of_two_dvd_sq {p : ℕ} (h : 2 ∣ p ^ 2) : 2 ∣ p :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
-- BOOK: end sqrt2-even

-- BOOK: begin sqrt2-core
-- 核心: 既約分数 p/q に対して p² = 2q² はあり得ない
theorem sqrt2_core (p q : ℕ) (hcop : Nat.gcd p q = 1) :
    p ^ 2 ≠ 2 * q ^ 2 := by
  intro h
  -- p は偶数。p = 2k と書く。
  have hp : 2 ∣ p := two_dvd_of_two_dvd_sq ⟨q ^ 2, h⟩
  obtain ⟨k, hk⟩ := hp
  -- BOOK: elide begin q も偶数になることを同様に示す
  have hq2 : q ^ 2 = 2 * k ^ 2 := by
    have : 2 * q ^ 2 = 4 * k ^ 2 := by rw [← h, hk]; ring
    omega
  have hq : 2 ∣ q := two_dvd_of_two_dvd_sq ⟨k ^ 2, hq2⟩
  -- BOOK: elide end
  -- p も q も偶数なら gcd は 2 以上 — 既約性と矛盾
  have : 2 ∣ Nat.gcd p q := Nat.dvd_gcd ⟨k, hk⟩ hq
  rw [hcop] at this
  omega
-- BOOK: end sqrt2-core

-- BOOK: begin sqrt2-mathlib
-- mathlib の一般定理(√n が無理数 ⟺ n は平方数でない)から
example : Irrational (Real.sqrt 2) := irrational_sqrt_two
-- BOOK: end sqrt2-mathlib

-- BOOK: begin sqrt2-rationalize
-- 有理化の心臓部: (√2 + 1)(√2 − 1) = 1
-- ゆえに 1/(√2 − 1) = √2 + 1(分母から根号が消える)
example : (Real.sqrt 2 + 1) * (Real.sqrt 2 - 1) = 1 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  ring_nf
  linarith [h2]
-- BOOK: end sqrt2-rationalize

-- BOOK: begin irrational-add
-- 無理数は有理数を足しても・掛けても(0以外)無理数のまま
example (q : ℚ) : Irrational (Real.sqrt 2 + q) :=
  irrational_sqrt_two.add_ratCast q

example : Irrational (2 * Real.sqrt 2) := by
  have h := irrational_sqrt_two.ratCast_mul
    (show (2 : ℚ) ≠ 0 by norm_num)
  simpa using h
-- BOOK: end irrational-add

-- BOOK: begin sqrt2-dense
-- 有理数の稠密性: どんな2つの実数の間にも有理数がある
example (x y : ℝ) (h : x < y) :
    ∃ q : ℚ, x < q ∧ (q : ℝ) < y :=
  exists_rat_btwn h
-- BOOK: end sqrt2-dense

end Handbook.C06
