/- 第37章 代数的トポロジー
   37.3 円周の基本群と応用 -/
import Mathlib

namespace Handbook.C37

-- BOOK: begin fta
-- 代数学の基本定理。次数 1 以上の複素係数多項式は根を持つ
example (p : Polynomial ℂ) (hp : 0 < p.degree) :
    ∃ z : ℂ, p.eval z = 0 :=
  Complex.exists_root hp

-- 具体例: x² + 1 は ℂ で根 i を持つ
example : (Polynomial.X ^ 2 + 1 : Polynomial ℂ).eval Complex.I = 0 := by
  simp [Complex.I_sq]
-- BOOK: end fta

-- BOOK: begin simply-connected
-- 単連結な空間ではすべてのループが1点に縮む
#check @SimplyConnectedSpace

-- ℝ は単連結(可縮なので)
example : SimplyConnectedSpace ℝ := by infer_instance

-- 円周は単連結でない。基本群が ℤ になるためである
#check @Circle
-- BOOK: end simply-connected

end Handbook.C37
