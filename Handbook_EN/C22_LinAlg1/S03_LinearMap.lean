/- Chapter 22: Linear algebra I
   22.4 Linear maps, kernel and image -/
import Mathlib

namespace Handbook.C22

-- BOOK: begin linmap
-- A linear map f : V →ₗ[ℝ] W preserves sums and scalar multiples
example (f : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))
    (v w : Fin 3 → ℝ) :
    f (v + w) = f v + f w :=
  f.map_add v w
-- BOOK: end linmap

-- BOOK: begin ker-inj
-- Injective ⟺ the kernel is just {0}.
-- The kernel measures injectivity of a linear map.
example (f : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) :
    LinearMap.ker f = ⊥ ↔ Function.Injective f :=
  LinearMap.ker_eq_bot
-- BOOK: end ker-inj

-- BOOK: begin rank-nullity
-- Rank--nullity: dim(image) + dim(kernel) = dim(domain)
example (f : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) :
    Module.finrank ℝ (LinearMap.range f)
      + Module.finrank ℝ (LinearMap.ker f) = 3 := by
  rw [LinearMap.finrank_range_add_finrank_ker]
  simp
-- BOOK: end rank-nullity

end Handbook.C22
