/- 第8章 関数の基礎
   8.2 グラフと像 -/
import Mathlib

namespace Handbook.C08

-- BOOK: begin image-def
open Set in
-- 像 f '' A = { f x | x ∈ A }。[-1, 1] の x² による像は [0, 1] に入る
example :
    (fun x : ℚ => x ^ 2) '' {x | -1 ≤ x ∧ x ≤ 1}
      ⊆ {y | 0 ≤ y ∧ y ≤ 1} := by
  rintro y ⟨x, ⟨hx1, hx2⟩, rfl⟩
  constructor
  · positivity
  · nlinarith
-- BOOK: end image-def

-- BOOK: begin image-eval
-- 有限集合の像は計算できる
#eval (Finset.range 5).image (fun n => n ^ 2)
-- 出力: {0, 1, 4, 9, 16}
-- BOOK: end image-eval

-- BOOK: begin image-comp
-- 合成の像は像の像: (g ∘ f) '' A = g '' (f '' A)
example (f g : ℚ → ℚ) (A : Set ℚ) :
    (g ∘ f) '' A = g '' (f '' A) :=
  Set.image_comp g f A
-- BOOK: end image-comp

-- BOOK: begin preimage-def
-- 逆像 f ⁻¹' B は「行き先が B に入る入力の全体」
example : (· * 2) ⁻¹' {6} = {(3 : ℤ)} := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  omega
-- BOOK: end preimage-def

end Handbook.C08
