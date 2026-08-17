/- 第4章 Lean 言語の基礎
   4.4 基本型 -/
import Mathlib

namespace Handbook.C04

-- BOOK: begin basic-sub
-- 同じ「引き算」でも型によって振る舞いが違う
#eval (3 - 5 : ℕ)  -- 出力: 0(自然数は 0 で切り捨て)
#eval (3 - 5 : ℤ)  -- 出力: -2
#eval (3 / 4 : ℚ)  -- 出力: 3/4
-- BOOK: end basic-sub

-- BOOK: begin basic-bool
-- Bool は計算の世界の真偽値。
-- 命題(Prop)は #eval できず、decide で Bool に落として計算する。
#eval decide (2 < 3)  -- 出力: true
#eval decide (3 ∣ 12) -- 出力: true
-- BOOK: end basic-bool

-- BOOK: begin basic-list
#eval "Lean " ++ "4"           -- 出力: "Lean 4"
#eval [1, 2, 3].map (· * 2)    -- 出力: [2, 4, 6]
#eval (List.range 5).sum       -- 出力: 10
-- BOOK: end basic-list

-- BOOK: begin basic-float
-- Float は近似の世界。0.1 + 0.2 は 0.3 に一致しない。
#eval (0.1 + 0.2 : Float)         -- 出力: 0.300000000000000044
#eval (0.1 + 0.2 : Float) == 0.3  -- 出力: false
#eval (1 / 10 + 2 / 10 : ℚ)       -- ℚ なら正確に 3/10
-- BOOK: end basic-float

-- BOOK: begin basic-coe
-- 狭い型から広い型へは ↑(強制)で移る
#check ((3 : ℕ) : ℤ)     -- ↑3 : ℤ
#eval ((3 : ℕ) : ℚ) / 4  -- 出力: 3/4(ℚ に移してから割る)

-- 強制をまたぐ等式は push_cast で整える
example (m n : ℕ) : ((m + n : ℕ) : ℤ) = m + n := by
  push_cast; ring
-- BOOK: end basic-coe

end Handbook.C04
