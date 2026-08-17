/- 第34章 関数解析
   34.5 正規直交基底とフーリエ展開 -/
import Mathlib

namespace Handbook.C34

-- BOOK: begin orthonormal
-- 正規直交系の2条件を、仮定から取り出して確かめる
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
-- 正規直交系での係数抽出。⟪v i, x⟫ がフーリエ係数にあたる
example (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ι : Type) (v : ι → E) (h : Orthonormal ℝ v) (i : ι) :
    inner ℝ (v i) (v i) = 1 := by
  rw [real_inner_self_eq_norm_sq, h.1 i]
  norm_num
-- BOOK: end bessel

-- BOOK: begin coefficient
-- 有限個の正規直交系での展開では、係数が内積で取り出せる
example (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ι : Type) [Fintype ι] (v : ι → E) (h : Orthonormal ℝ v)
    (l : ι → ℝ) (i : ι) :
    inner ℝ (∑ j, l j • v j) (v i) = l i := by
  simpa using h.inner_left_fintype l i
-- BOOK: end coefficient

-- BOOK: begin hilbert-basis
-- Hilbert 基底: 正規直交で、張った空間が全体で稠密なもの
#check @HilbertBasis

-- 有限次元では通常の正規直交基底として実現される
#check @OrthonormalBasis
-- BOOK: end hilbert-basis

end Handbook.C34
