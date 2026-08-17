/- 第6章 数と式
   6.1b 数の拡張の動機 — 解けない方程式が解けるようになる -/
import Mathlib

namespace Handbook.C06

-- BOOK: begin ext-nat-int
-- ℕ では x + 2 = 1 が解けない。ℤ へ広げると解ける
example : ¬ ∃ n : ℕ, n + 2 = 1 := by
  rintro ⟨n, hn⟩
  omega

example : ∃ n : ℤ, n + 2 = 1 := ⟨-1, by ring⟩
-- BOOK: end ext-nat-int

-- BOOK: begin ext-int-rat
-- ℤ では 2x = 1 が解けない。ℚ へ広げると解ける
example : ¬ ∃ n : ℤ, 2 * n = 1 := by
  rintro ⟨n, hn⟩
  omega

example : ∃ q : ℚ, 2 * q = 1 := ⟨1 / 2, by norm_num⟩
-- BOOK: end ext-int-rat

-- BOOK: begin ext-dense
-- ℚ は ℝ の中で稠密。どの2実数の間にも有理数がある
example (x y : ℝ) (h : x < y) :
    ∃ q : ℚ, x < (q : ℝ) ∧ (q : ℝ) < y :=
  exists_rat_btwn h
-- BOOK: end ext-dense

-- BOOK: begin ext-gap
-- それでも ℚ には穴がある。x² = 2 の解が無い
example : ¬ ∃ q : ℚ, q ^ 2 = 2 := by
  rintro ⟨q, hq⟩
  have hnn : (0 : ℝ) ≤ ((|q| : ℚ) : ℝ) := by
    exact_mod_cast abs_nonneg q
  have hsq : ((|q| : ℚ) : ℝ) ^ 2 = 2 := by
    push_cast
    rw [sq_abs]
    exact_mod_cast hq
  have h2 : ((|q| : ℚ) : ℝ) = Real.sqrt 2 := by
    rw [← hsq, Real.sqrt_sq hnn]
  exact irrational_sqrt_two ⟨|q|, h2⟩
-- BOOK: end ext-gap

end Handbook.C06
