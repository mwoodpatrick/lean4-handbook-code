/- 第35章 数論
   35.7 Fermat の最終定理 -/
import Mathlib

namespace Handbook.C35

-- BOOK: begin flt-statement
-- Fermat の最終定理の主張。n ≥ 3 では自明でない解がない
#check @FermatLastTheorem

-- 指数 n を固定した版
#check @FermatLastTheoremFor
-- BOOK: end flt-statement

-- BOOK: begin flt-four
-- n = 4 の場合。Fermat 自身が無限降下法で証明した
example : FermatLastTheoremFor 4 :=
  fermatLastTheoremFour

-- n = 3 の場合。Euler(1770)。mathlib にも形式化済み
example : FermatLastTheoremFor 3 :=
  fermatLastTheoremThree
-- BOOK: end flt-four

-- BOOK: begin pythagorean
-- n = 2 では解が無限にある(ピタゴラス数)
example : 3 ^ 2 + 4 ^ 2 = 5 ^ 2 := by norm_num
example : 5 ^ 2 + 12 ^ 2 = 13 ^ 2 := by norm_num
example : 8 ^ 2 + 15 ^ 2 = 17 ^ 2 := by norm_num

-- 一般式: (m²-k²)² + (2mk)² = (m²+k²)²
example (m k : ℤ) :
    (m ^ 2 - k ^ 2) ^ 2 + (2 * m * k) ^ 2 = (m ^ 2 + k ^ 2) ^ 2 := by
  ring
-- BOOK: end pythagorean

end Handbook.C35
