/- English edition source: Handbook/C23_LinAlg2/S01_Matrix.lean. -/
import Mathlib

namespace Handbook.C23

open Matrix

-- BOOK: begin matrix-def
-- A matrix is entered as !![...] and multiplied with *
def A : Matrix (Fin 2) (Fin 2) ℚ := !![1, 2; 3, 4]
def B : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 1, 0]

#eval A 0 1    -- output: 2 (the entry in row 1, column 2)
#eval A * B    -- output: !![2, 1; 4, 3]
-- BOOK: end matrix-def

-- BOOK: begin matrix-noncomm
-- Matrix multiplication is not commutative
#eval B * A    -- output: !![3, 4; 1, 2] (different from A * B)
-- BOOK: end matrix-noncomm

-- BOOK: begin matrix-id
-- The identity matrix 1 is the multiplicative identity. Transposition
-- swaps rows and columns.
example (M : Matrix (Fin 2) (Fin 2) ℚ) : 1 * M = M := one_mul M

#eval (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℚ)ᵀ
-- output: !![1, 3; 2, 4]
-- BOOK: end matrix-id

end Handbook.C23
