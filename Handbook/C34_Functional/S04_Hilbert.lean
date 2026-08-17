/- 第34章 関数解析
   34.4 Hilbert 空間と正射影・Riesz の表現定理 -/
import Mathlib

namespace Handbook.C34

-- BOOK: begin cauchy-schwarz
-- Cauchy–Schwarz の不等式。第15章の内積の一般化
example (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) : inner ℝ x y ≤ ‖x‖ * ‖y‖ :=
  real_inner_le_norm x y

-- 内積からノルムが決まる。‖x‖² = ⟪x, x⟫
example (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : E) : inner ℝ x x = ‖x‖ ^ 2 :=
  real_inner_self_eq_norm_sq x
-- BOOK: end cauchy-schwarz

-- BOOK: begin pythagoras
-- 展開公式。内積が 0 なら三平方の定理になる
example (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * inner ℝ x y + ‖y‖ ^ 2 :=
  norm_add_sq_real x y

-- 直交する 2 ベクトルでは三平方の定理が成り立つ
example (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) (h : inner ℝ x y = (0 : ℝ)) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [norm_add_sq_real, h]
  ring
-- BOOK: end pythagoras

-- BOOK: begin projection
-- 正射影: 閉部分空間へ「最も近い点」を返す有界線形作用素
noncomputable example (E : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (U : Submodule ℝ E)
    [U.HasOrthogonalProjection] : E →L[ℝ] E :=
  U.starProjection
-- BOOK: end projection

-- BOOK: begin riesz
-- Riesz の表現定理: Hilbert 空間の連続双対は自分自身と等長同型
noncomputable example (E : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] :
    E ≃ₗᵢ⋆[ℝ] StrongDual ℝ E :=
  InnerProductSpace.toDual ℝ E
-- BOOK: end riesz

end Handbook.C34
