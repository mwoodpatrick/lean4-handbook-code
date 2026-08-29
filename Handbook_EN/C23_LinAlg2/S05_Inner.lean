/- English edition source: Handbook/C23_LinAlg2/S05_Inner.lean. -/
import Mathlib

namespace Handbook.C23

-- BOOK: begin orthonormal
-- Orthonormal: a family of mutually orthogonal vectors of length 1
#check @Orthonormal

-- An orthonormal basis; the coordinates are read off by inner products
#check @OrthonormalBasis
-- BOOK: end orthonormal

-- BOOK: begin gram-schmidt
-- Gram--Schmidt builds an orthonormal basis from any basis
#check @InnerProductSpace.gramSchmidtOrthonormalBasis

-- it subtracts, one at a time, the components along the earlier vectors
#check @InnerProductSpace.gramSchmidt
-- BOOK: end gram-schmidt

-- BOOK: begin projection
-- Orthogonal projection: the map to the nearest point of a subspace
#check @Submodule.orthogonalProjectionOnto

-- The decomposition V = W ⊕ W^⊥ of an inner product space
#check @Submodule.orthogonal
-- BOOK: end projection

end Handbook.C23
