/- English edition source: Handbook/C14_Integers/S04_ZMod.lean. -/
import Mathlib

namespace Handbook.C14

-- BOOK: begin zmod-clock
-- A congruence is an equality in the “12-hour clock world” ZMod 12
example : (7 : ZMod 12) + 8 = 3 := by decide

example : (5 : ZMod 7) * 3 = 1 := by decide
-- BOOK: end zmod-clock

-- BOOK: begin zmod-dvd
-- “A multiple of 3” is the same as “maps to 0 in ZMod 3”
example (n : ℕ) : (n : ZMod 3) = 0 ↔ 3 ∣ n :=
  ZMod.natCast_eq_zero_iff n 3
-- BOOK: end zmod-dvd

-- BOOK: begin zmod-digit
-- Principle of casting out nines: since 10 ≡ 1 (mod 9), only the digit
-- sum remains
example : (10 : ZMod 9) = 1 := by decide

-- Example: the remainder of 3^100 modulo 7. Use 3⁶ ≡ 1 to reduce the
-- power.
example : (3 : ZMod 7) ^ 100 = 4 := by
  have h : (3 : ZMod 7) ^ 6 = 1 := by decide
  calc (3 : ZMod 7) ^ 100
      = ((3 : ZMod 7) ^ 6) ^ 16 * 3 ^ 4 := by ring
    _ = 1 ^ 16 * 3 ^ 4 := by rw [h]
    _ = 4 := by decide
-- BOOK: end zmod-digit

-- BOOK: begin casting-out
-- Casting out nines: check a huge product by its remainder modulo 9
#eval 123456789 % 9                -- output: 0
#eval (123456789 * 987654321) % 9  -- output: 0 (consistent with 0×0)

example : (123456789 * 987654321) % 9 = 0 := by decide
-- BOOK: end casting-out

-- BOOK: begin dvd-six
-- Example: the product of three consecutive integers is divisible by 6.
-- Discharge all six cases in ZMod 6 with decide, then transfer the
-- result back to integers.
example (n : ℤ) : 6 ∣ n * (n + 1) * (n + 2) := by
  have h : ∀ m : ZMod 6, m * (m + 1) * (m + 2) = 0 := by
    decide
  have h2 := h (n : ZMod 6)
  rwa [show ((n : ZMod 6) * (↑n + 1) * (↑n + 2))
      = ((n * (n + 1) * (n + 2) : ℤ) : ZMod 6) by
        push_cast; ring,
    ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
-- BOOK: end dvd-six

-- BOOK: begin rsa-toy
-- Toy RSA: n = 33, e = 3, d = 7. Encrypt plaintext 2, then decrypt it.
example : (2 ^ 3 : ZMod 33) = 8 := by decide

example : (8 ^ 7 : ZMod 33) = 2 := by decide
-- BOOK: end rsa-toy

end Handbook.C14
