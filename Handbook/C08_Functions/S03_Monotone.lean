/- 第8章 関数の基礎
   8.3 単調性 -/
import Mathlib

namespace Handbook.C08

-- BOOK: begin mono-inj
-- 狭義単調な関数は単射である(順序が値の衝突を禁じる)
example (f : ℚ → ℚ) (hf : StrictMono f) :
    Function.Injective f :=
  hf.injective
-- BOOK: end mono-inj

-- BOOK: begin fun-seq
-- 数列は「ℕ からの関数」にすぎない(第12章の再解釈)
def seq (n : ℕ) : ℚ := n ^ 2

#eval [seq 0, seq 1, seq 2, seq 3]  -- 出力: [0, 1, 4, 9]

-- 単調性の語彙もそのまま使える
example : StrictMono seq := by
  intro a b h
  unfold seq
  exact_mod_cast Nat.pow_lt_pow_left h (by norm_num)
-- BOOK: end fun-seq

-- BOOK: begin mono-def
-- 狭義単調増加の定義どおりの証明
example : StrictMono (fun x : ℚ => 2 * x + 1) := by
  intro a b hab
  dsimp only
  linarith
-- BOOK: end mono-def

-- BOOK: begin mono-comp
-- 単調関数の合成は単調
example (f g : ℚ → ℚ) (hf : StrictMono f) (hg : StrictMono g) :
    StrictMono (g ∘ f) :=
  hg.comp hf
-- BOOK: end mono-comp

end Handbook.C08
