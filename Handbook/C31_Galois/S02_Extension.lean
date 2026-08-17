/- 第31章 体論とガロア理論
   31.2 拡大次数の塔 / 31.3 分解体と代数閉包 -/
import Mathlib

namespace Handbook.C31

-- BOOK: begin tower-law
-- 次数の塔: 拡大を重ねると次数は掛け算になる
example (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] [Module.Finite K L] [Module.Finite L M] :
    Module.finrank K L * Module.finrank L M
      = Module.finrank K M :=
  Module.finrank_mul_finrank K L M
-- BOOK: end tower-law

-- BOOK: begin adjoin
-- 添加: K に α を付け加えた最小の中間体
#check @IntermediateField.adjoin

-- 次数1の拡大は元の体そのもの
#check @IntermediateField.finrank_bot
-- BOOK: end adjoin

-- BOOK: begin splitting
-- 分解体: その多項式が1次式の積に分かれる最小の拡大
#check @Polynomial.IsSplittingField

-- 代数閉包: すべての多項式が分解する拡大。常に存在する(Zorn)
#check @AlgebraicClosure
-- BOOK: end splitting

-- BOOK: begin finite-field
-- 有限体の位数は必ず素数冪である
example (K : Type) [Field K] [Fintype K] :
    ∃ p, CharP K p ∧ ∃ n : ℕ+, Nat.Prime p ∧
      Fintype.card K = p ^ (n : ℕ) :=
  FiniteField.card' K
-- BOOK: end finite-field

end Handbook.C31
