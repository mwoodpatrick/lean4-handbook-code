/- English edition source: Handbook/C39_AlgGeometry/S01_Varieties.lean. -/
import Mathlib

namespace Handbook.C39

-- BOOK: begin curves
-- An algebraic curve: the zero set of a polynomial.
-- The circle is x² + y² − 1 = 0.
example (x y : ℝ) : x ^ 2 + y ^ 2 - 1 = 0 ↔ x ^ 2 + y ^ 2 = 1 := by
  constructor <;> intro h <;> linarith

-- the point (0, 0) on the elliptic curve y² = x³ − x
example : (0 : ℝ) ^ 2 = 0 ^ 3 - 0 := by norm_num

-- the point (1, 0) lies on it too
example : (0 : ℝ) ^ 2 = 1 ^ 3 - 1 := by norm_num
-- BOOK: end curves

-- BOOK: begin mvpolynomial
-- The ring of polynomials in several variables; the number of
-- variables is carried by the type
#check @MvPolynomial

-- evaluating the two-variable polynomial X₀ + X₁ at (3, 4) gives 7
example :
    MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (3 : ℤ) else 4)
      (MvPolynomial.X 0 + MvPolynomial.X 1) = 7 := by
  simp
-- BOOK: end mvpolynomial

end Handbook.C39
