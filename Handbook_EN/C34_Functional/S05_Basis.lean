/- English edition source: Handbook/C34_Functional/S05_Basis.lean. -/
import Mathlib

namespace Handbook.C34

-- BOOK: begin orthonormal
-- Extract the two conditions of an orthonormal family from the
-- hypothesis
example (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ι : Type) (v : ι → E) (h : Orthonormal ℝ v) (i : ι) :
    ‖v i‖ = 1 :=
  h.1 i

example (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ι : Type) (v : ι → E) (h : Orthonormal ℝ v) (i j : ι)
    (hij : i ≠ j) : inner ℝ (v i) (v j) = 0 :=
  h.2 hij
-- BOOK: end orthonormal

-- BOOK: begin bessel
-- Reading off coefficients in an orthonormal family: ⟪v, x⟫ is the
-- Fourier coefficient
example (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ι : Type) (v : ι → E) (h : Orthonormal ℝ v) (i : ι) :
    inner ℝ (v i) (v i) = 1 := by
  rw [real_inner_self_eq_norm_sq, h.1 i]
  norm_num
-- BOOK: end bessel

-- BOOK: begin coefficient
-- In a finite orthonormal expansion the coefficients are recovered
-- by inner products
example (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ι : Type) [Fintype ι] (v : ι → E) (h : Orthonormal ℝ v)
    (l : ι → ℝ) (i : ι) :
    inner ℝ (∑ j, l j • v j) (v i) = l i := by
  simpa using h.inner_left_fintype l i
-- BOOK: end coefficient

-- BOOK: begin hilbert-basis
-- A Hilbert basis: an orthonormal family whose span is dense in
-- the whole space
#check @HilbertBasis

-- in finite dimension it is realized as an orthonormal basis
#check @OrthonormalBasis
-- BOOK: end hilbert-basis

end Handbook.C34
