/- 第8章 関数の基礎
   8.5 合成と可換図式 -/
import Mathlib

namespace Handbook.C08

-- BOOK: begin comp-def
-- 合成 g ∘ f。単射の合成は単射。
example (f g : ℚ → ℚ) (hf : Function.Injective f)
    (hg : Function.Injective g) :
    Function.Injective (g ∘ f) :=
  hg.comp hf

-- 全射の合成は全射
example (f g : ℚ → ℚ) (hf : Function.Surjective f)
    (hg : Function.Surjective g) :
    Function.Surjective (g ∘ f) :=
  hg.comp hf
-- BOOK: end comp-def

-- BOOK: begin comp-noncomm
-- 合成は順序に敏感: 「2倍して1足す」と「1足して2倍」は別物
#eval (fun x : ℚ => 2 * x + 1) 5    -- 出力: 11
#eval (fun x : ℚ => 2 * (x + 1)) 5  -- 出力: 12

example : ∃ x : ℚ, 2 * x + 1 ≠ 2 * (x + 1) :=
  ⟨0, by norm_num⟩
-- BOOK: end comp-noncomm

-- BOOK: begin comp-assoc
-- 合成は結合的。可換図式の土台となる事実。
example (f g h : ℚ → ℚ) : (h ∘ g) ∘ f = h ∘ (g ∘ f) :=
  Function.comp_assoc h g f
-- BOOK: end comp-assoc

-- BOOK: begin functions-exercises
-- 演習: 単射の証明・値の計算・合成の性質
example : Function.Injective (fun x : ℚ => x - 4) := by
  intro a b h
  dsimp only at h
  linarith

example : (fun x : ℚ => x ^ 2 + 1) 3 = 10 := by norm_num

example (f : ℚ → ℚ) (hf : Function.Injective f) :
    Function.Injective (f ∘ f) :=
  hf.comp hf
-- BOOK: end functions-exercises

end Handbook.C08
