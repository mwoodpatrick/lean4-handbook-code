/- 第40章 mathlib の歩き方
   40.1 全体構造 / 40.2 命名規約 -/
import Mathlib

namespace Handbook.C40

-- BOOK: begin naming-read
-- 名前は「結論を左から読み下したもの」。記号を英単語に置換する
#check @Nat.add_comm      -- add + comm : a + b = b + a
#check @mul_pos           -- mul, pos   : 0 < a → 0 < b → 0 < a * b
#check @abs_add_le        -- abs, add, le : |a + b| ≤ |a| + |b|
#check @Set.mem_setOf_eq  -- mem, setOf : (a ∈ {x | p x}) = p a
-- BOOK: end naming-read

-- BOOK: begin naming-dot
-- 名前空間つきの名前はドット記法で使える
example (X Y Z : Type) [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : X → Y) (g : Y → Z)
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (g ∘ f) :=
  hg.comp hf   -- Continuous.comp hg hf と同じ

-- 先頭の型が名前空間と一致するとき .comp が使える
#check @Continuous.comp
-- BOOK: end naming-dot

-- BOOK: begin naming-direction
-- of は「右から左」を表す。le_of_lt は < から ≤ を作る
example (a b : ℕ) (h : a < b) : a ≤ b := le_of_lt h

-- iff は同値。両向きに .mp と .mpr で使える
example (a b : ℕ) : a ≤ b ↔ a < b + 1 := Nat.lt_succ_iff.symm
-- BOOK: end naming-direction

end Handbook.C40
