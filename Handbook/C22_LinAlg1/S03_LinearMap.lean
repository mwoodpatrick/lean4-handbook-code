/- 第22章 線形代数I — ベクトル空間と線形写像
   22.5 線形写像と核・像 / 22.6 次元定理 -/
import Mathlib

namespace Handbook.C22

-- BOOK: begin linmap
-- 線形写像 f : V →ₗ[ℝ] W は加法とスカラー倍を保つ
example (f : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))
    (v w : Fin 3 → ℝ) :
    f (v + w) = f v + f w :=
  f.map_add v w
-- BOOK: end linmap

-- BOOK: begin ker-inj
-- 単射 ⟺ 核が {0} だけ。核が線形写像の単射性を測る。
example (f : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) :
    LinearMap.ker f = ⊥ ↔ Function.Injective f :=
  LinearMap.ker_eq_bot
-- BOOK: end ker-inj

-- BOOK: begin rank-nullity
-- 次元定理(rank–nullity): dim(像) + dim(核) = dim(定義域)
example (f : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) :
    Module.finrank ℝ (LinearMap.range f)
      + Module.finrank ℝ (LinearMap.ker f) = 3 := by
  rw [LinearMap.finrank_range_add_finrank_ker]
  simp
-- BOOK: end rank-nullity

end Handbook.C22
