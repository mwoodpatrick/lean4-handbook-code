/- 第21章 無限級数
   21.3 収束判定法 / 21.4 絶対収束 -/
import Mathlib

namespace Handbook.C21

-- BOOK: begin comparison
-- 比較判定法: 収束する級数で上から押さえれば収束する
example (f g : ℕ → ℝ) (hg : Summable g)
    (h : ∀ n, ‖f n‖ ≤ g n) : Summable f :=
  Summable.of_norm_bounded hg h
-- BOOK: end comparison

-- BOOK: begin abs-conv
-- 絶対収束するなら収束する
example (f : ℕ → ℝ) (h : Summable (fun n => |f n|)) :
    Summable f :=
  h.of_abs
-- BOOK: end abs-conv

-- BOOK: begin p-series
-- p 級数 Σ 1/nᵖ は p > 1 のとき収束、p ≤ 1 のとき発散
example : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
  Real.summable_one_div_nat_pow.mpr (by norm_num)

-- p = 1(調和級数)は発散: 収束の同値条件 1 < p を満たさない
example : ¬ Summable (fun n : ℕ => 1 / (n : ℝ) ^ 1) := by
  rw [Real.summable_one_div_nat_pow]; norm_num
-- BOOK: end p-series

-- BOOK: begin ratio-test
-- 比判定法(ダランベール): 比が 1 未満の定数以下ならば収束
example (f : ℕ → ℝ) (r : ℝ) (hr₁ : r < 1)
    (h : ∀ n, ‖f (n + 1)‖ ≤ r * ‖f n‖) :
    Summable f :=
  summable_of_ratio_norm_eventually_le hr₁
    (Filter.Eventually.of_forall h)
-- BOOK: end ratio-test

end Handbook.C21
