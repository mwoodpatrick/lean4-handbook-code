/- 第17章 実数と数列の極限
   17.3 数列の収束 — ε-N の定義を読む・書く -/
import Mathlib

namespace Handbook.C17

-- BOOK: begin epsn-def
-- ε-N 論法の定義をそのまま書き下す
def TendsToNat (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε
-- BOOK: end epsn-def

-- BOOK: begin epsn-proof
-- 1/(n+1) → 0 を定義どおり証明する
theorem one_div_tendsTo_zero :
    TendsToNat (fun n => 1 / (n + 1)) 0 := by
  intro ε hε
  -- アルキメデスの性質: 1/ε を超える自然数 N が取れる
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  use N
  intro n hn
  have h1 : (0 : ℝ) < n + 1 := by positivity
  rw [sub_zero, abs_of_pos (by positivity), div_lt_iff₀ h1]
  -- BOOK: elide begin 1/ε < N ≤ n < n+1 から 1 < ε(n+1) を得る
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : 1 / ε < (n : ℝ) + 1 := by linarith
  rw [div_lt_iff₀ hε] at h2
  exact h2.trans_eq (mul_comm _ _)
  -- BOOK: elide end
-- BOOK: end epsn-proof

-- BOOK: begin epsn-const
-- 定数列 c, c, c, … は c に収束する(N は何でもよい)
example (c : ℝ) : TendsToNat (fun _ => c) c := by
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  simpa using hε
-- BOOK: end epsn-const

end Handbook.C17
