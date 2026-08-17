/- 第14章 整数の世界
   14.1 割り算の原理と整除 -/
import Mathlib

namespace Handbook.C14

-- BOOK: begin div-mod
-- 割り算の原理: a = b·(a/b) + a%b、余りは b 未満
example (a b : ℕ) : b * (a / b) + a % b = a := Nat.div_add_mod a b

example (a b : ℕ) (hb : 0 < b) : a % b < b := Nat.mod_lt a hb
-- BOOK: end div-mod

-- BOOK: begin dvd-basic
-- 整除 a ∣ b の定義は「∃ c, b = a * c」
example : (3 : ℕ) ∣ 12 := ⟨4, rfl⟩

example (a b c : ℕ) (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c :=
  hab.trans hbc
-- BOOK: end dvd-basic

end Handbook.C14
