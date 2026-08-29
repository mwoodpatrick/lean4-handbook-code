/- English edition source: Handbook/C14_Integers/S01_Division.lean. -/
import Mathlib

namespace Handbook.C14

-- BOOK: begin div-mod
-- Euclidean division: a = b·(a/b) + a%b, with remainder less than b
example (a b : ℕ) : b * (a / b) + a % b = a := Nat.div_add_mod a b

example (a b : ℕ) (hb : 0 < b) : a % b < b := Nat.mod_lt a hb
-- BOOK: end div-mod

-- BOOK: begin dvd-basic
-- Divisibility a ∣ b means “∃ c, b = a * c”
example : (3 : ℕ) ∣ 12 := ⟨4, rfl⟩

example (a b c : ℕ) (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c :=
  hab.trans hbc
-- BOOK: end dvd-basic

end Handbook.C14
