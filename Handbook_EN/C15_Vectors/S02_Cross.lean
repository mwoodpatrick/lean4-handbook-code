/- English edition source: Handbook/C15_Vectors/S02_Cross.lean. -/
import Mathlib

namespace Handbook.C15

open scoped Matrix

-- BOOK: begin dot-eval
-- The inner product in components:
-- (1,2)·(3,-1) = 1·3 + 2·(-1) = 1
#eval (![1, 2] : Fin 2 → ℤ) ⬝ᵥ ![3, -1]  -- output: 1
-- BOOK: end dot-eval

-- BOOK: begin vec-components
-- In components: sums and scalar multiples act componentwise
-- (displayed as a list)
#eval List.ofFn ((![1, 2] : Fin 2 → ℤ) + ![3, 4])
-- output: [4, 6]
#eval List.ofFn ((3 : ℤ) • (![1, 2] : Fin 2 → ℤ))
-- output: [3, 6]

-- A component-wise equality can also be closed by decide
example : (![1, 2] : Fin 2 → ℤ) + ![3, 4] = ![4, 6] := by
  decide
-- BOOK: end vec-components

-- BOOK: begin vec-area
-- In two dimensions the determinant gives the "signed area":
-- the parallelogram spanned by (3,1) and (2,5) has area
-- 3·5 − 1·2 = 13
example :
    (!![3, 1; 2, 5] : Matrix (Fin 2) (Fin 2) ℤ).det = 13 := by
  rw [Matrix.det_fin_two_of]
  norm_num
-- BOOK: end vec-area

-- BOOK: begin vec-cross
-- The cross product (in three dimensions) is anticommutative,
-- and the cross product of a vector with itself is 0.
example (u v : Fin 3 → ℝ) : -(u ⨯₃ v) = v ⨯₃ u :=
  cross_anticomm u v

example (u : Fin 3 → ℝ) : u ⨯₃ u = 0 :=
  cross_self u
-- BOOK: end vec-cross

-- BOOK: begin vec-cross-dot
-- The cross product is orthogonal to both original vectors
-- (the scalar triple product is 0)
example (u v : Fin 3 → ℝ) : u ⬝ᵥ u ⨯₃ v = 0 :=
  dot_self_cross u v
-- BOOK: end vec-cross-dot

-- BOOK: begin vec-perp-solve
-- Worked example: find the x making (x, 6) orthogonal to (1, 2)
example (x : ℚ) :
    (![x, 6] : Fin 2 → ℚ) ⬝ᵥ ![1, 2] = 0 ↔ x = -12 := by
  simp only [dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · intro h; linarith
  · rintro rfl; norm_num
-- BOOK: end vec-perp-solve

-- BOOK: begin vec-section
-- The point dividing in the ratio 2:1: computing P = (1/3)a + (2/3)b
#eval List.ofFn (((1 : ℚ)/3) • (![0, 0] : Fin 2 → ℚ)
  + ((2 : ℚ)/3) • ![6, 3])
-- output: [4, 2]
-- BOOK: end vec-section

-- BOOK: begin vectors-exercises
-- Exercises: testing orthogonality and homogeneity of the norm
example : (![1, 2] : Fin 2 → ℤ) ⬝ᵥ ![2, -1] = 0 := by decide

example (x : EuclideanSpace ℝ (Fin 2)) :
    ‖(2 : ℝ) • x‖ = 2 * ‖x‖ := by
  rw [norm_smul, Real.norm_eq_abs]
  norm_num
-- BOOK: end vectors-exercises

end Handbook.C15
