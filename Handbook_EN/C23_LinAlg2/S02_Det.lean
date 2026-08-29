/- English edition source: Handbook/C23_LinAlg2/S02_Det.lean. -/
import Mathlib

namespace Handbook.C23

-- BOOK: begin det
-- The determinant of a 2×2 matrix is ad − bc
example : (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℚ).det = -2 := by
  rw [Matrix.det_fin_two_of]
  norm_num

-- The determinant is multiplicative
example (M N : Matrix (Fin 2) (Fin 2) ℚ) :
    (M * N).det = M.det * N.det :=
  Matrix.det_mul M N
-- BOOK: end det

-- BOOK: begin det-props
-- The determinant of the identity is 1 (it does not change volume)
example : (1 : Matrix (Fin 2) (Fin 2) ℚ).det = 1 := Matrix.det_one

-- The determinant is unchanged by transposition
example (M : Matrix (Fin 2) (Fin 2) ℚ) : M.transpose.det = M.det :=
  Matrix.det_transpose M
-- BOOK: end det-props

-- BOOK: begin inverse
-- If the determinant is invertible there is an inverse matrix
example (M : Matrix (Fin 2) (Fin 2) ℚ) (h : IsUnit M.det) :
    M * M⁻¹ = 1 :=
  Matrix.mul_nonsing_inv M h

-- The general theory of eigenvalues is stated for Module.End
#check @Module.End.HasEigenvalue
-- BOOK: end inverse

-- BOOK: begin eigen-def
-- An eigenvector: T v = μ v (scaling by μ alone).
-- HasEigenvector μ v says that v is an eigenvector for μ.
example {V : Type} [AddCommGroup V] [Module ℝ V]
    (T : Module.End ℝ V) (μ : ℝ) (v : V)
    (h : T.HasEigenvector μ v) : T v = μ • v :=
  h.apply_eq_smul
-- BOOK: end eigen-def

end Handbook.C23
