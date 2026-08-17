/- 第35章 数論
   35.1 平方剰余と相互法則 -/
import Mathlib

namespace Handbook.C35

-- p = 7 を固定して具体値を計算するための素数性インスタンス
instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

-- BOOK: begin legendre-values
-- ルジャンドル記号: 平方剰余なら 1、非剰余なら -1、割り切れれば 0
example : legendreSym 7 2 = 1 := by decide
example : legendreSym 7 3 = -1 := by decide
example : legendreSym 7 7 = 0 := by decide

-- 2 は mod 7 の平方剰余: 3² = 9 ≡ 2
example : (3 : ZMod 7) ^ 2 = 2 := by decide
-- BOOK: end legendre-values

-- BOOK: begin euler-criterion
-- オイラーの規準: a が平方剰余 ⟺ a^((p-1)/2) = 1
example (p : ℕ) [Fact p.Prime] (a : ZMod p) (ha : a ≠ 0) :
    IsSquare a ↔ a ^ (p / 2) = 1 :=
  ZMod.euler_criterion p ha
-- BOOK: end euler-criterion

-- BOOK: begin quad-reciprocity
-- 平方剰余の相互法則。2つの奇素数の平方剰余性が結び付く
example (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym q p * legendreSym p q = (-1) ^ (p / 2 * (q / 2)) :=
  legendreSym.quadratic_reciprocity hp hq hpq

-- 第1補充法則: -1 が平方剰余かは p mod 4 で決まる
example (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p (-1) = ZMod.χ₄ p :=
  legendreSym.at_neg_one hp
-- BOOK: end quad-reciprocity

end Handbook.C35
