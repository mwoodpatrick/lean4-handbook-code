/- 第14章 整数の世界
   14.4 合同式と ZMod -/
import Mathlib

namespace Handbook.C14

-- BOOK: begin zmod-clock
-- 合同式は「12 時間時計の世界 ZMod 12」の等式である
example : (7 : ZMod 12) + 8 = 3 := by decide

example : (5 : ZMod 7) * 3 = 1 := by decide
-- BOOK: end zmod-clock

-- BOOK: begin zmod-dvd
-- 「3 の倍数」は「ZMod 3 に写すと 0」と同じこと
example (n : ℕ) : (n : ZMod 3) = 0 ↔ 3 ∣ n :=
  ZMod.natCast_eq_zero_iff n 3
-- BOOK: end zmod-dvd

-- BOOK: begin zmod-digit
-- 九去法の原理: 10 ≡ 1 (mod 9) なので桁の和だけが残る
example : (10 : ZMod 9) = 1 := by decide

-- 例題: 3^100 を 7 で割った余り。3⁶ ≡ 1 で冪を潰す。
example : (3 : ZMod 7) ^ 100 = 4 := by
  have h : (3 : ZMod 7) ^ 6 = 1 := by decide
  calc (3 : ZMod 7) ^ 100
      = ((3 : ZMod 7) ^ 6) ^ 16 * 3 ^ 4 := by ring
    _ = 1 ^ 16 * 3 ^ 4 := by rw [h]
    _ = 4 := by decide
-- BOOK: end zmod-digit

-- BOOK: begin casting-out
-- 九去法: 巨大な積の検算を「9で割った余り」で行う
#eval 123456789 % 9                -- 出力: 0
#eval (123456789 * 987654321) % 9  -- 出力: 0(0×0 と整合)

example : (123456789 * 987654321) % 9 = 0 := by decide
-- BOOK: end casting-out

-- BOOK: begin dvd-six
-- 例題: 連続する3整数の積は 6 の倍数。
-- ZMod 6 の全6パターンを decide で潰し、整数へ持ち帰る。
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
-- 玩具の RSA: n = 33, e = 3, d = 7。平文 2 を暗号化→復号。
example : (2 ^ 3 : ZMod 33) = 8 := by decide

example : (8 ^ 7 : ZMod 33) = 2 := by decide
-- BOOK: end rsa-toy

end Handbook.C14
