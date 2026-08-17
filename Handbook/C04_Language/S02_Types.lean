/- 第4章 Lean 言語の基礎
   4.2 型と関数 — すべての式は型を持つ -/
import Mathlib

namespace Handbook.C04

-- BOOK: begin types-fun
def double (n : ℕ) : ℕ := 2 * n

#check double    -- double : ℕ → ℕ
#eval double 21  -- 出力: 42
-- BOOK: end types-fun

-- BOOK: begin types-curry
-- 多引数関数は「関数を返す関数」である(カリー化)
def add3 (a b c : ℕ) : ℕ := a + b + c

#check add3      -- add3 : ℕ → ℕ → ℕ → ℕ
#check add3 1    -- add3 1 : ℕ → ℕ → ℕ(部分適用)
#eval add3 1 2 3 -- 出力: 6
-- BOOK: end types-curry

-- BOOK: begin types-lambda
-- 名前のない関数(ラムダ式)。fun 引数 => 本体。
#eval (fun x : ℕ => x ^ 2) 9          -- 出力: 81
#eval [1, 2, 3].map (fun n => n * n)  -- 出力: [1, 4, 9]

-- 関数合成 ∘ : (f ∘ g) x = f (g x)
#eval (double ∘ double) 3  -- 出力: 12
-- BOOK: end types-lambda

-- BOOK: begin types-hof
-- 関数を受け取る関数(高階関数)
#eval [1, 2, 3, 4, 5].filter (· % 2 = 1)  -- 出力: [1, 3, 5]
#eval [1, 2, 3, 4].foldl (· + ·) 0        -- 出力: 10
#eval (List.range 6).map (2 ^ ·)          -- [1, 2, 4, …, 32]
-- BOOK: end types-hof

-- BOOK: begin types-type
-- 型自身も式であり、型を持つ
#check ℕ     -- ℕ : Type
#check Type  -- Type : Type 1
-- BOOK: end types-type

end Handbook.C04
