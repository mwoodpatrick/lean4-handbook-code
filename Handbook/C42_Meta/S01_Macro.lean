/- 第42章 メタプログラミングと tactic 開発
   42.2 構文木と macro — 記法の自作 -/
import Mathlib

namespace Handbook.C42

-- BOOK: begin macro-term
-- 記法の自作: my_double x は x + x に展開される
macro "my_double" x:term : term => `($x + $x)

#eval my_double 21  -- 出力: 42
-- BOOK: end macro-term

-- BOOK: begin notation
-- notation は中置記法を作る。優先順位を数字で指定する
notation:65 a " ⊕' " b => (a + b) * 2

example : (3 ⊕' 4) = 14 := by norm_num
-- BOOK: end notation

-- BOOK: begin macro-tactic
-- tactic の自作(最小例): 連言を分解して両側を assumption で閉じる
macro "easy_and" : tactic =>
  `(tactic| (constructor <;> assumption))

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  easy_and
-- BOOK: end macro-tactic

-- BOOK: begin macro-rules
-- macro_rules は既存の記法に規則を足す。引数の個数で分岐できる
syntax "triple" term : term
macro_rules
  | `(triple $x) => `($x + $x + $x)

#eval triple 7  -- 出力: 21
-- BOOK: end macro-rules

end Handbook.C42
