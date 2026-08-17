/- 第22章 線形代数I — ベクトル空間と線形写像
   22.3 線形独立と基底 / 22.4 次元 -/
import Mathlib

namespace Handbook.C22

-- BOOK: begin basis-dim
-- ℝ² の標準基底
#check Module.Basis.finTwoProd ℝ  -- Basis (Fin 2) ℝ (ℝ × ℝ)

-- 次元(有限次元)は finrank
example : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp

example : Module.finrank ℝ (Fin 3 → ℝ) = 3 := by simp
-- BOOK: end basis-dim

end Handbook.C22
