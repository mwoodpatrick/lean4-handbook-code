/- 第13章 場合の数と確率
   13.1 数え上げの原理 -/
import Mathlib

namespace Handbook.C13

open Finset

-- BOOK: begin count-card
#eval (range 10).card  -- 出力: 10

-- 積の法則: 直積の要素数は要素数の積
example (s t : Finset ℕ) : (s ×ˢ t).card = s.card * t.card :=
  Finset.card_product s t

-- 和の法則: 重なりのない合併の要素数は和
example (s t : Finset ℕ) (h : Disjoint s t) :
    (s ∪ t).card = s.card + t.card :=
  Finset.card_union_of_disjoint h
-- BOOK: end count-card

-- BOOK: begin count-concrete
-- 和菓子3種・洋菓子4種: 「1つ選ぶ」は 7 通り、「1つずつ選ぶ」は 12 通り
#eval (range 3 ∪ (range 7 \ range 3)).card       -- 出力: 7
#eval ((range 3) ×ˢ (range 4)).card              -- 出力: 12

-- シャツ3 × ズボン2 = 6 通り。積の法則の実演。
example : ((range 3) ×ˢ (range 2)).card = 6 := by decide
-- BOOK: end count-concrete

end Handbook.C13
