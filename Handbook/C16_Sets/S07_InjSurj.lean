/- 第16章 集合と写像
   16.4 単射・全射・全単射 -/
import Mathlib

namespace Handbook.C16

-- BOOK: begin injsurj-def
-- 単射: 値が同じなら元も同じ。「潰さない」ことを言う
example (f : ℕ → ℕ) (hf : Function.Injective f) (a b : ℕ)
    (h : f a = f b) : a = b := hf h

-- 全射: どの値も誰かの像である。「取りこぼさない」
#check @Function.Surjective

-- 全単射は両方
#check @Function.Bijective
-- BOOK: end injsurj-def

-- BOOK: begin injsurj-example
-- n ↦ n + 1 は単射
example : Function.Injective (fun n : ℕ => n + 1) := by
  intro a b h
  simpa using h

-- しかし全射ではない。0 は誰の像でもない
example : ¬ Function.Surjective (fun n : ℕ => n + 1) := by
  intro h
  obtain ⟨a, ha⟩ := h 0
  simp at ha
-- BOOK: end injsurj-example

-- BOOK: begin inverse
-- 全単射であることと、両側逆写像を持つことは同値
example (f : ℕ → ℕ) (hf : Function.Bijective f) :
    ∃ g, Function.LeftInverse g f ∧ Function.RightInverse g f :=
  Function.bijective_iff_has_inverse.mp hf

-- 単射なら左逆写像 invFun が作れる(始域が空でないこと)
#check @Function.leftInverse_invFun
-- BOOK: end inverse

-- BOOK: begin comp-inj
-- 単射どうしの合成は単射。全射も同様
#check @Function.Injective.comp
#check @Function.Surjective.comp

-- 単射なら f a = f b を a = b に書き換えられる
#check @Function.Injective.eq_iff
-- BOOK: end comp-inj

end Handbook.C16
