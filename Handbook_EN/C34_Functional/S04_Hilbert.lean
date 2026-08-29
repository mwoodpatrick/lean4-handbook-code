/- English edition source: Handbook/C34_Functional/S04_Hilbert.lean. -/
import Mathlib

namespace Handbook.C34

-- BOOK: begin cauchy-schwarz
-- The Cauchy--Schwarz inequality, generalizing the inner product of
-- Chapter 15
example (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) : inner ℝ x y ≤ ‖x‖ * ‖y‖ :=
  real_inner_le_norm x y

-- The norm is determined by the inner product: ‖x‖² = ⟪x, x⟫
example (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : E) : inner ℝ x x = ‖x‖ ^ 2 :=
  real_inner_self_eq_norm_sq x
-- BOOK: end cauchy-schwarz

-- BOOK: begin pythagoras
-- Expanding ‖x + y‖² brings out the inner product term
example (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * inner ℝ x y + ‖y‖ ^ 2 :=
  norm_add_sq_real x y

-- when that term vanishes (orthogonality) the Pythagorean
-- theorem remains
example (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) (h : inner ℝ x y = (0 : ℝ)) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [norm_add_sq_real, h]
  ring
-- BOOK: end pythagoras

-- BOOK: begin projection
-- Orthogonal projection is a bounded linear operator returning the
-- closest point in a closed subspace.
noncomputable example (E : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (U : Submodule ℝ E)
    [U.HasOrthogonalProjection] : E →L[ℝ] E :=
  U.starProjection
-- BOOK: end projection

-- BOOK: begin riesz
-- Riesz representation theorem: the continuous dual of a Hilbert space
-- is isometrically isomorphic to the space itself.
noncomputable example (E : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] :
    E ≃ₗᵢ⋆[ℝ] StrongDual ℝ E :=
  InnerProductSpace.toDual ℝ E
-- BOOK: end riesz

end Handbook.C34
