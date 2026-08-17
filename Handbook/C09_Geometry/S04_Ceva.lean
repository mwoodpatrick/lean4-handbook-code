/- 第9章 平面図形と初等幾何
   9.8b チェバとメネラウス — 比の積で語る定理 -/
import Mathlib

namespace Handbook.C09

-- BOOK: begin ceva-identity
-- チェバの定理の代数的な核。3つの比の積が 1 になる。
-- 分点を t で表すと、恒等式として検算できる。
example (x y z : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    (x / y) * (y / z) * (z / x) = 1 := by
  field_simp
-- BOOK: end ceva-identity

-- BOOK: begin menelaus-sign
-- メネラウスでは比の積が -1 になる。符号が2つの定理を分ける。
example (x y z : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    (x / y) * (y / z) * (-(z / x)) = -1 := by
  field_simp
-- BOOK: end menelaus-sign

-- BOOK: begin ceva-centroid
-- 重心は3中線の交点。座標では頂点の平均になる
example (a b c : ℝ × ℝ) :
    ((a.1 + b.1 + c.1) / 3, (a.2 + b.2 + c.2) / 3)
      = (1 / 3 : ℝ) • (a.1 + b.1 + c.1, a.2 + b.2 + c.2) := by
  simp [Prod.smul_mk]
  constructor <;> ring
-- BOOK: end ceva-centroid

end Handbook.C09
