/- 第44章 ケーススタディ
   44.2 数値で確かめる / 44.5 別証明と一般化 -/
import Handbook.C12_Induction.S03_Sums
import Handbook.C44_CaseStudy.S01_Nicomachus

namespace Handbook.C44

open Finset

-- BOOK: begin explore-eval
-- まず数値で確かめる。主張が正しいかを疑う段階
#eval (List.range 6).map fun n =>
  (∑ k ∈ range (n + 1), k ^ 3, (∑ k ∈ range (n + 1), k) ^ 2)

-- 小さい n では decide で機械的に確認できる
example : ∑ k ∈ range 5, k ^ 3 = (∑ k ∈ range 5, k) ^ 2 := by
  decide
-- BOOK: end explore-eval

-- BOOK: begin explore-closed
-- ガウスの和の閉じた形。第12章の 2S = n(n+1) から出る
theorem sum_range_closed (n : ℕ) :
    2 * ∑ k ∈ range (n + 1), k = n * (n + 1) :=
  Handbook.C12.gauss_sum n

-- 閉じた形を使うと、主張は 4·Σk³ = n²(n+1)² と書き換わる
theorem nicomachus_closed (n : ℕ) :
    4 * ∑ k ∈ range (n + 1), k ^ 3 = (n * (n + 1)) ^ 2 := by
  have h := nicomachus n
  have h2 := sum_range_closed n
  calc 4 * ∑ k ∈ range (n + 1), k ^ 3
      = (2 * ∑ k ∈ range (n + 1), k) ^ 2 := by rw [h]; ring
    _ = (n * (n + 1)) ^ 2 := by rw [h2]
-- BOOK: end explore-closed

-- BOOK: begin explore-axioms
-- 証明が sorry に依存していないことを確認する
#print axioms nicomachus
#print axioms nicomachus_closed
-- BOOK: end explore-axioms

end Handbook.C44
