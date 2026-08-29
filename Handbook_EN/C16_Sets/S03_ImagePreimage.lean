/- English edition source: Handbook/C16_Sets/S03_ImagePreimage.lean. -/
import Mathlib

namespace Handbook.C16

-- BOOK: begin image-preimage
-- Images preserve inclusion
example (f : ℕ → ℕ) (A B : Set ℕ) (h : A ⊆ B) :
    f '' A ⊆ f '' B :=
  Set.image_mono h

-- The image of a preimage is contained in the original set
example (f : ℕ → ℕ) (B : Set ℕ) :
    f '' (f ⁻¹' B) ⊆ B :=
  Set.image_preimage_subset f B
-- BOOK: end image-preimage

-- BOOK: begin preimage-ops
-- Preimages interact perfectly with set operations (all are preserved
-- by equality)
example (f : ℕ → ℕ) (A B : Set ℕ) :
    f ⁻¹' (A ∩ B) = f ⁻¹' A ∩ f ⁻¹' B :=
  Set.preimage_inter
-- BOOK: end preimage-ops

-- BOOK: begin image-inter-sub
-- For images of intersections we can state only an inclusion (equality
-- is false in general)
example (f : ℕ → ℕ) (A B : Set ℕ) :
    f '' (A ∩ B) ⊆ f '' A ∩ f '' B :=
  Set.image_inter_subset f A B

-- Injectivity restores equality
example (f : ℕ → ℕ) (hf : Function.Injective f) (A B : Set ℕ) :
    f '' (A ∩ B) = f '' A ∩ f '' B :=
  Set.image_inter hf
-- BOOK: end image-inter-sub

end Handbook.C16
