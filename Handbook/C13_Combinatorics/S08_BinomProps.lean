/- 第13章 場合の数と確率
   13.3b 二項係数の性質 -/
import Mathlib

namespace Handbook.C13

-- BOOK: begin bin-pascal
-- パスカルの規則。三角形の各項は上の2項の和である
example (n k : ℕ) :
    Nat.choose (n + 1) (k + 1)
      = Nat.choose n k + Nat.choose n (k + 1) :=
  Nat.choose_succ_succ n k
-- BOOK: end bin-pascal

-- BOOK: begin bin-symm
-- 対称性。k 個選ぶことと n-k 個残すことは同じ
example (n k : ℕ) (h : k ≤ n) :
    Nat.choose n k = Nat.choose n (n - k) :=
  (Nat.choose_symm h).symm
-- BOOK: end bin-symm

-- BOOK: begin bin-rowsum
-- 各行の和は 2^n。部分集合の総数に一致する
example (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Nat.choose n k = 2 ^ n :=
  Nat.sum_range_choose n
-- BOOK: end bin-rowsum

-- BOOK: begin bin-vandermonde
-- ヴァンデルモンドの畳み込み。2つの箱から合わせて k 個選ぶ。
-- 右辺は「i + j = k となる組 (i, j)」を走る和である
example (m n k : ℕ) :
    Nat.choose (m + n) k
      = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k,
          Nat.choose m ij.1 * Nat.choose n ij.2 :=
  Nat.add_choose_eq m n k
-- BOOK: end bin-vandermonde

end Handbook.C13
