/- 第4章 Lean 言語の基礎
   4.8 依存型と宇宙入門 -/
import Mathlib

namespace Handbook.C04

-- BOOK: begin univ-tower
-- 型の型、その型、… は無限の塔をなす(宇宙)
#check ℕ       -- ℕ : Type
#check Type    -- Type : Type 1
#check Type 1  -- Type 1 : Type 2
#check Prop    -- Prop : Type
-- BOOK: end univ-tower

-- BOOK: begin univ-dependent
-- 依存型: 戻り値の「型」が引数の「値」に依存する
def Tuple (n : ℕ) : Type := Fin n → ℚ

def allZero (n : ℕ) : Tuple n := fun _ => 0

#check allZero 3  -- allZero 3 : Tuple 3
#check allZero 5  -- allZero 5 : Tuple 5(型が変わった)
-- BOOK: end univ-dependent

-- BOOK: begin univ-poly
-- 宇宙多相: どの階の型にも働く定義は宇宙変数 u を持つ
universe u

def twice {α : Type u} (f : α → α) (a : α) : α := f (f a)

#eval twice (· + 10) 5         -- 出力: 25
#eval twice (List.cons 0) [1]  -- 出力: [0, 0, 1]
-- BOOK: end univ-poly

-- BOOK: begin univ-subtype
-- 部分型 {x // P x}: 値に「条件を満たす証明」を同梱する
def half : {q : ℚ // 0 < q} := ⟨1 / 2, by norm_num⟩

#eval half.val    -- 出力: 1/2(値の部分)
#check half.prop  -- 0 < 1/2 の証明の部分
-- BOOK: end univ-subtype

-- BOOK: begin lang-exercises
-- 演習: 本章の道具で定義と検証を1往復する
def triple (n : ℕ) : ℕ := 3 * n

def isEven (n : ℕ) : Bool := n % 2 == 0

#eval triple 14  -- 出力: 42
#eval isEven 7   -- 出力: false

example : triple 4 = 12 := rfl
example (n : ℕ) : triple (n + 1) = triple n + 3 := by
  unfold triple
  ring
-- BOOK: end lang-exercises

end Handbook.C04
