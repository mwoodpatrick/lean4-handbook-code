/- English edition source: Handbook/C21_Series/S02_Convergence.lean. -/
import Mathlib

namespace Handbook.C21

-- BOOK: begin comparison
-- The comparison test: bounded above by a convergent series,
-- it converges
example (f g : ℕ → ℝ) (hg : Summable g)
    (h : ∀ n, ‖f n‖ ≤ g n) : Summable f :=
  Summable.of_norm_bounded hg h
-- BOOK: end comparison

-- BOOK: begin abs-conv
-- Absolute convergence implies convergence
example (f : ℕ → ℝ) (h : Summable (fun n => |f n|)) :
    Summable f :=
  h.of_abs
-- BOOK: end abs-conv

-- BOOK: begin p-series
-- The p-series Σ 1/nᵖ converges for p > 1 and diverges for p ≤ 1
example : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
  Real.summable_one_div_nat_pow.mpr (by norm_num)

-- p = 1 (the harmonic series) diverges: it fails the condition
-- 1 < p that is equivalent to convergence
example : ¬ Summable (fun n : ℕ => 1 / (n : ℝ) ^ 1) := by
  rw [Real.summable_one_div_nat_pow]; norm_num
-- BOOK: end p-series

-- BOOK: begin ratio-test
-- The ratio test (d'Alembert): it converges if the ratio stays
-- below a constant less than 1
example (f : ℕ → ℝ) (r : ℝ) (hr₁ : r < 1)
    (h : ∀ n, ‖f (n + 1)‖ ≤ r * ‖f n‖) :
    Summable f :=
  summable_of_ratio_norm_eventually_le hr₁
    (Filter.Eventually.of_forall h)
-- BOOK: end ratio-test

end Handbook.C21
