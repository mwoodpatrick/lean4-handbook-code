/- English edition source: Handbook/C34_Functional/S02_Operator.lean. -/
import Mathlib

namespace Handbook.C34

-- BOOK: begin op-norm
-- Defining bound of the operator norm: ‖f x‖ ≤ ‖f‖ * ‖x‖ always holds.
example (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E →L[ℝ] F) (x : E) : ‖f x‖ ≤ ‖f‖ * ‖x‖ :=
  f.le_opNorm x

-- Conversely, an estimate of that shape gives an upper bound for
-- the operator norm
example (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E →L[ℝ] F) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ x, ‖f x‖ ≤ M * ‖x‖) : ‖f‖ ≤ M :=
  f.opNorm_le_bound hM h
-- BOOK: end op-norm

-- BOOK: begin op-comp
-- For a composition the operator norm is bounded by the product
example (E F G : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : F →L[ℝ] G) (f : E →L[ℝ] F) : ‖g.comp f‖ ≤ ‖g‖ * ‖f‖ :=
  g.opNorm_comp_le f

-- A bounded linear operator is continuous. Unlike in finite dimensions,
-- boundedness is a genuine condition.
example (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E →L[ℝ] F) : Continuous f :=
  f.continuous
-- BOOK: end op-comp

end Handbook.C34
