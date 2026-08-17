/- 第5章 証明の基本
   5.1 命題と Prop -/
import Mathlib

namespace Handbook.C05

-- BOOK: begin prop-type
-- 命題は Prop 型の項である
#check 2 + 2 = 4       -- 2 + 2 = 4 : Prop
#check 2 + 2 = 5       -- これも立派な命題(偽だが)
#check ∀ n : ℕ, 0 ≤ n  -- ∀ (n : ℕ), 0 ≤ n : Prop
-- BOOK: end prop-type

-- BOOK: begin prop-proof
-- 証明とは、命題という型を持つ項を作ることである
theorem two_add_two : 2 + 2 = 4 := rfl

#check two_add_two     -- two_add_two : 2 + 2 = 4
-- BOOK: end prop-proof

-- BOOK: begin prop-truefalse
-- 最も単純な命題: True(証明は trivial)と False(証明はない)
example : True := trivial

-- False からは何でも従う(爆発律)
example (P : Prop) (h : False) : P := h.elim
-- BOOK: end prop-truefalse

end Handbook.C05
