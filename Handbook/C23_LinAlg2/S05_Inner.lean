/- 第23章 線形代数II
   23.7 内積空間と直交化 -/
import Mathlib

namespace Handbook.C23

-- BOOK: begin orthonormal
-- 正規直交系: 長さ1で互いに直交する族
#check @Orthonormal

-- 正規直交基底。座標が内積で読み取れる
#check @OrthonormalBasis
-- BOOK: end orthonormal

-- BOOK: begin gram-schmidt
-- Gram–Schmidt の直交化。任意の基底から正規直交基底を作る
#check @InnerProductSpace.gramSchmidtOrthonormalBasis

-- 逐次的に「これまでの成分を引く」操作そのもの
#check @InnerProductSpace.gramSchmidt
-- BOOK: end gram-schmidt

-- BOOK: begin projection
-- 直交射影。部分空間へ最も近い点を落とす写像
#check @Submodule.orthogonalProjectionOnto

-- 内積空間の分解 V = W ⊕ W^⊥
#check @Submodule.orthogonal
-- BOOK: end projection

end Handbook.C23
