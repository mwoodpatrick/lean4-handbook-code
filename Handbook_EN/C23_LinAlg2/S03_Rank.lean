/- English edition source: Handbook/C23_LinAlg2/S03_Rank.lean. -/
import Mathlib

namespace Handbook.C23

-- BOOK: begin rank-def
-- The rank is defined as the dimension of the image of the linear
-- map given by the matrix
#check @Matrix.rank

-- The rank does not exceed the number of columns
#check @Matrix.rank_le_card_width
-- BOOK: end rank-def

-- BOOK: begin rank-nullity
-- Rank--nullity (Chapter 22): the dimension of the image plus the
-- dimension of the kernel is the dimension of the domain
#check @LinearMap.finrank_range_add_finrank_ker
-- BOOK: end rank-nullity

-- BOOK: begin solve-system
-- Ax = b: mulVec applies a matrix to a vector
#check @Matrix.mulVec

-- det M = 0 is equivalent to having a non-trivial solution.
-- The existence of a solution is decided by a single number.
#check @Matrix.exists_mulVec_eq_zero_iff
-- BOOK: end solve-system

-- BOOK: begin invertible-iff
-- A matrix is invertible exactly when its determinant is a unit
example {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) :
    IsUnit M ↔ IsUnit M.det :=
  Matrix.isUnit_iff_isUnit_det M
-- BOOK: end invertible-iff

end Handbook.C23
