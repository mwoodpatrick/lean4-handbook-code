/- 第16章 集合と写像 — 数学の言語
   16.3 像と逆像 -/
import Mathlib

namespace Handbook.C16

-- BOOK: begin image-preimage
-- 像は包含を保つ
example (f : ℕ → ℕ) (A B : Set ℕ) (h : A ⊆ B) :
    f '' A ⊆ f '' B :=
  Set.image_mono h

-- 「逆像の像」は元の集合に含まれる
example (f : ℕ → ℕ) (B : Set ℕ) :
    f '' (f ⁻¹' B) ⊆ B :=
  Set.image_preimage_subset f B
-- BOOK: end image-preimage

-- BOOK: begin preimage-ops
-- 逆像は集合演算と最高に相性がよい(すべて等号で保存)
example (f : ℕ → ℕ) (A B : Set ℕ) :
    f ⁻¹' (A ∩ B) = f ⁻¹' A ∩ f ⁻¹' B :=
  Set.preimage_inter
-- BOOK: end preimage-ops

-- BOOK: begin image-inter-sub
-- 像は共通部分を「含む」ことしか言えない(等号は一般には偽)
example (f : ℕ → ℕ) (A B : Set ℕ) :
    f '' (A ∩ B) ⊆ f '' A ∩ f '' B :=
  Set.image_inter_subset f A B

-- 単射なら等号が回復する
example (f : ℕ → ℕ) (hf : Function.Injective f) (A B : Set ℕ) :
    f '' (A ∩ B) = f '' A ∩ f '' B :=
  Set.image_inter hf
-- BOOK: end image-inter-sub

end Handbook.C16
