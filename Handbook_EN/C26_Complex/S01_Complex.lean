/- English edition source: Handbook/C26_Complex/S01_Complex.lean. -/
import Mathlib

namespace Handbook.C26

open Complex

-- BOOK: begin complex-i
-- The imaginary unit I, with I² = −1.
example : I ^ 2 = -1 := I_sq

#eval (2 + 3 * I) * (2 - 3 * I)  -- Output: 13 + 0i
-- BOOK: end complex-i

-- BOOK: begin complex-conj
-- z * conj z = |z|²
example (z : ℂ) : z * (starRingEnd ℂ) z = Complex.normSq z :=
  Complex.mul_conj z

-- (2+3i)(2−3i) = 13 = 2² + 3² (a hint of the two-square theorem)
example : (2 + 3 * I) * (2 - 3 * I) = 13 := by
  simp [Complex.ext_iff]; norm_num
-- BOOK: end complex-conj

-- BOOK: begin euler
-- Euler's formula e^(iz) = cos z + i sin z
example (z : ℂ) : exp (z * I) = cos z + sin z * I :=
  (cos_add_sin_I z).symm
-- BOOK: end euler

-- BOOK: begin euler-identity
-- e^(iπ) + 1 = 0
example : exp ((Real.pi : ℂ) * I) + 1 = 0 := by
  rw [Complex.exp_pi_mul_I]; ring
-- BOOK: end euler-identity

-- BOOK: begin alg-closed
-- The fundamental theorem of algebra: ℂ is algebraically closed
example : IsAlgClosed ℂ := Complex.isAlgClosed
-- BOOK: end alg-closed

-- BOOK: begin liouville
-- Liouville’s theorem: a bounded entire function (complex
-- differentiable on the whole plane) is constant.
example (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hb : Bornology.IsBounded (Set.range f)) (z w : ℂ) :
    f z = f w :=
  hf.apply_eq_apply_of_bounded hb z w
-- BOOK: end liouville

end Handbook.C26
