/- 第35章 数論
   35.2 2平方和定理 -/
import Mathlib

namespace Handbook.C35

-- BOOK: begin two-squares
-- フェルマーの2平方和定理(クリスマス定理):
-- p ≢ 3 (mod 4) の素数は2つの平方数の和で書ける
example (p : ℕ) [Fact p.Prime] (hp : p % 4 ≠ 3) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p :=
  Nat.Prime.sq_add_sq hp
-- BOOK: end two-squares

-- BOOK: begin two-squares-examples
-- 具体例: 4k+1 型の素数は必ず書ける
example : 1 ^ 2 + 2 ^ 2 = 5 := by norm_num
example : 2 ^ 2 + 3 ^ 2 = 13 := by norm_num
example : 1 ^ 2 + 4 ^ 2 = 17 := by norm_num

-- 4k+3 型の 7 は書けない。平方数は mod 4 で 0 か 1 のため
example : ∀ a b : ZMod 4, a ^ 2 + b ^ 2 ≠ 3 := by decide
-- BOOK: end two-squares-examples

-- BOOK: begin gaussian
-- ガウス整数環 ℤ[i] ではノルムが積を保つ。2平方和の背景
example (z w : GaussianInt) :
    (z * w).norm = z.norm * w.norm :=
  Zsqrtd.norm_mul z w

-- 5 = (2+i)(2-i) と分解する。ℤ では素数でも ℤ[i] では素でない
example : (⟨2, 1⟩ : GaussianInt) * ⟨2, -1⟩ = 5 := by decide
-- BOOK: end gaussian

end Handbook.C35
