/- 第26章 複素解析
   26.1 複素数 / 26.4 オイラーの公式 -/
import Mathlib

namespace Handbook.C26

open Complex

-- BOOK: begin complex-i
-- 虚数単位 I。I² = -1。
example : I ^ 2 = -1 := I_sq

#eval (2 + 3 * I) * (2 - 3 * I)  -- 出力: 13 + 0i
-- BOOK: end complex-i

-- BOOK: begin complex-conj
-- 共役との積は絶対値の2乗(実数): z * conj z = |z|²
example (z : ℂ) : z * (starRingEnd ℂ) z = Complex.normSq z :=
  Complex.mul_conj z

-- (2+3i)(2-3i) = 13 = 2² + 3²(2平方和定理への伏線)
example : (2 + 3 * I) * (2 - 3 * I) = 13 := by
  simp [Complex.ext_iff]; norm_num
-- BOOK: end complex-conj

-- BOOK: begin euler
-- オイラーの公式 e^(zi) = cos z + i sin z
example (z : ℂ) : exp (z * I) = cos z + sin z * I :=
  (cos_add_sin_I z).symm
-- BOOK: end euler

-- BOOK: begin euler-identity
-- オイラーの等式 e^(iπ) + 1 = 0(五大定数が一列に並ぶ)
example : exp ((Real.pi : ℂ) * I) + 1 = 0 := by
  rw [Complex.exp_pi_mul_I]; ring
-- BOOK: end euler-identity

-- BOOK: begin alg-closed
-- 代数学の基本定理: ℂ は代数閉体
example : IsAlgClosed ℂ := Complex.isAlgClosed
-- BOOK: end alg-closed

-- BOOK: begin liouville
-- Liouville の定理: 有界な整関数(全平面で微分可能)は定数
example (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hb : Bornology.IsBounded (Set.range f)) (z w : ℂ) :
    f z = f w :=
  hf.apply_eq_apply_of_bounded hb z w
-- BOOK: end liouville

end Handbook.C26
