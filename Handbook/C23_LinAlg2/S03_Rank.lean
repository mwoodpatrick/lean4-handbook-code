/- 第23章 線形代数II
   23.2 連立1次方程式と階数 -/
import Mathlib

namespace Handbook.C23

-- BOOK: begin rank-def
-- 階数は「行列が定める線形写像の像の次元」として定義される
#check @Matrix.rank

-- 階数は列の本数を超えない
#check @Matrix.rank_le_card_width
-- BOOK: end rank-def

-- BOOK: begin rank-nullity
-- 次元定理(第22章)。像の次元と核の次元の和が全体の次元
#check @LinearMap.finrank_range_add_finrank_ker
-- BOOK: end rank-nullity

-- BOOK: begin solve-system
-- Ax = b の左辺。mulVec が行列とベクトルの積
#check @Matrix.mulVec

-- det M = 0 と「非自明な解を持つ」は同値。
-- 連立方程式の解の存在が1つの数で判定できる
#check @Matrix.exists_mulVec_eq_zero_iff
-- BOOK: end solve-system

-- BOOK: begin invertible-iff
-- 行列が可逆であることと行列式が単元であることは同値
example {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) :
    IsUnit M ↔ IsUnit M.det :=
  Matrix.isUnit_iff_isUnit_det M
-- BOOK: end invertible-iff

end Handbook.C23
