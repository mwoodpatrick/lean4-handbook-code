/- 第23章 線形代数II
   23.5 固有多項式と対角化 -/
import Mathlib

namespace Handbook.C23

-- BOOK: begin charpoly
-- 固有多項式 det(XI - M)。その根が固有値である
#check @Matrix.charpoly

-- 次数は行列のサイズに等しい
#check @Matrix.charpoly_degree_eq_dim
-- BOOK: end charpoly

-- BOOK: begin eigen-root
-- 固有値であることと固有多項式の根であることは同値。
-- 固有値の探索が多項式の根の探索に変わる
#check @Module.End.hasEigenvalue_iff_isRoot
-- BOOK: end eigen-root

-- BOOK: begin cayley-hamilton
-- Cayley–Hamilton: 行列は自分自身の固有多項式を満たす。
-- M の高い冪が低い冪の線形結合に落ちる
#check @Matrix.aeval_self_charpoly
-- BOOK: end cayley-hamilton

-- BOOK: begin trace
-- 跡は対角成分の和。固有値の総和に等しい
#check @Matrix.trace

-- 積の順序を入れ替えても跡は変わる。
-- ゆえに基底を取り替えても跡は不変である
example {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℚ) :
    (M * N).trace = (N * M).trace :=
  Matrix.trace_mul_comm M N
-- BOOK: end trace

-- BOOK: begin spectral
-- スペクトル定理: エルミート行列は直交行列で対角化できる
#check @Matrix.IsHermitian
#check @Matrix.IsHermitian.spectral_theorem
-- BOOK: end spectral

end Handbook.C23
