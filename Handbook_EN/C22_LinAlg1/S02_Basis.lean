/- Chapter 22: Linear algebra I
   22.3 Bases and dimension -/
import Mathlib

namespace Handbook.C22

-- BOOK: begin basis-dim
-- The standard basis of ℝ²
#check Module.Basis.finTwoProd ℝ   -- Basis (Fin 2) ℝ (ℝ × ℝ)

-- the dimension (in the finite-dimensional case) is finrank
example : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
example : Module.finrank ℝ (Fin 3 → ℝ) = 3 := by simp
-- BOOK: end basis-dim

end Handbook.C22
