/- English edition source: Handbook/C23_LinAlg2/S04_Diag.lean. -/
import Mathlib

namespace Handbook.C23

-- BOOK: begin charpoly
-- The characteristic polynomial det(λI − M); its roots are the
-- eigenvalues
#check @Matrix.charpoly

-- its degree equals the size of the matrix
#check @Matrix.charpoly_degree_eq_dim
-- BOOK: end charpoly

-- BOOK: begin eigen-root
-- An eigenvalue is a root of the characteristic polynomial.
-- Finding eigenvalues becomes finding roots of a polynomial.
#check @Module.End.hasEigenvalue_iff_isRoot
-- BOOK: end eigen-root

-- BOOK: begin cayley-hamilton
-- Cayley--Hamilton: a matrix satisfies its own characteristic
-- polynomial, so high powers of M reduce to low ones.
#check @Matrix.aeval_self_charpoly
-- BOOK: end cayley-hamilton

-- BOOK: begin trace
-- The trace is the sum of the diagonal entries, equal to the sum
-- of the eigenvalues
#check @Matrix.trace

-- The trace is unchanged when the order of a product is swapped,
-- so it is also unchanged by a change of basis
example {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℚ) :
    (M * N).trace = (N * M).trace :=
  Matrix.trace_mul_comm M N
-- BOOK: end trace

-- BOOK: begin spectral
-- The spectral theorem: a Hermitian matrix is diagonalizable
#check @Matrix.IsHermitian
#check @Matrix.IsHermitian.spectral_theorem
-- BOOK: end spectral

end Handbook.C23
