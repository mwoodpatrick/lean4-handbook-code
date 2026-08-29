/- English edition source: Handbook/C08_Functions/S02_Image.lean. -/
import Mathlib

namespace Handbook.C08

-- BOOK: begin image-def
open Set in
-- The image f '' A = { f x | x ∈ A }.
-- The image of [-1, 1] under x² lies in [0, 1]
example :
    (fun x : ℚ => x ^ 2) '' {x | -1 ≤ x ∧ x ≤ 1}
      ⊆ {y | 0 ≤ y ∧ y ≤ 1} := by
  rintro y ⟨x, ⟨hx1, hx2⟩, rfl⟩
  constructor
  · positivity
  · nlinarith
-- BOOK: end image-def

-- BOOK: begin image-eval
-- The image of a finite set can be computed
#eval (Finset.range 5).image (fun n => n ^ 2)
-- output: {0, 1, 4, 9, 16}
-- BOOK: end image-eval

-- BOOK: begin image-comp
-- The image of a composition is the image of the image:
-- (g ∘ f) '' A = g '' (f '' A)
example (f g : ℚ → ℚ) (A : Set ℚ) :
    (g ∘ f) '' A = g '' (f '' A) :=
  Set.image_comp g f A
-- BOOK: end image-comp

-- BOOK: begin preimage-def
-- The preimage f ⁻¹' B is the set of inputs landing in B
example : (· * 2) ⁻¹' {6} = {(3 : ℤ)} := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  omega
-- BOOK: end preimage-def

end Handbook.C08
