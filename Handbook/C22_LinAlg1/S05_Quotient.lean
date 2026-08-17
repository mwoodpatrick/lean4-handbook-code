/- 第22章 線形代数I
   22.7 商空間・直和・双対空間 -/
import Mathlib

namespace Handbook.C22

-- BOOK: begin quotient-space
-- 商空間 V/W。部分空間で割るのに追加条件は要らない——
-- ベクトル空間の加法が可換だから全部分空間が「正規」である
#check @Submodule.Quotient.mk

-- 第一同型定理: V/ker f ≅ im f(群・環と同じ形)
#check @LinearMap.quotKerEquivRange
-- BOOK: end quotient-space

-- BOOK: begin dimension-formula
-- 次元の包除原理: dim(U+W) + dim(U∩W) = dim U + dim W
#check @Submodule.finrank_sup_add_finrank_inf_eq

-- 補空間の存在。V = U ⊕ W と分解できる W が必ずある
#check @IsCompl
-- BOOK: end dimension-formula

-- BOOK: begin dual-space
-- 双対空間: V から係数体への線形写像全体。これもベクトル空間
#check @Module.Dual

-- 有限次元なら次元が等しい。無限次元では真に大きくなる
#check @Module.rank
-- BOOK: end dual-space

end Handbook.C22
