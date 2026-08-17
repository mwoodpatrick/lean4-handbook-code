/- 第23章 線形代数II — 行列・行列式・固有値
   23.1 行列と演算 -/
import Mathlib

namespace Handbook.C23

open Matrix

-- BOOK: begin matrix-def
-- 行列は !![...] 記法。積は * で書ける。
def A : Matrix (Fin 2) (Fin 2) ℚ := !![1, 2; 3, 4]
def B : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 1, 0]

#eval A 0 1    -- 出力: 2(1行2列目の成分)
#eval A * B    -- 出力: !![2, 1; 4, 3]
-- BOOK: end matrix-def

-- BOOK: begin matrix-noncomm
-- 行列の積は可換でない
#eval B * A    -- 出力: !![3, 4; 1, 2](A * B と異なる)
-- BOOK: end matrix-noncomm

-- BOOK: begin matrix-id
-- 単位行列 1 は積の単位元。転置は行と列を入れ替える。
example (M : Matrix (Fin 2) (Fin 2) ℚ) : 1 * M = M := one_mul M

#eval (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℚ)ᵀ
-- 出力: !![1, 3; 2, 4](行と列が入れ替わる)
-- BOOK: end matrix-id

end Handbook.C23
