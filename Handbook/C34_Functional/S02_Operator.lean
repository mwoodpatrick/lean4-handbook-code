/- 第34章 関数解析
   34.2 有界線形作用素と作用素ノルム -/
import Mathlib

namespace Handbook.C34

-- BOOK: begin op-norm
-- 作用素ノルムの定義的性質: ‖f x‖ ≤ ‖f‖ * ‖x‖ が常に成り立つ
example (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E →L[ℝ] F) (x : E) : ‖f x‖ ≤ ‖f‖ * ‖x‖ :=
  f.le_opNorm x

-- 逆に、その形の評価があれば作用素ノルムの上界が得られる
example (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E →L[ℝ] F) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ x, ‖f x‖ ≤ M * ‖x‖) : ‖f‖ ≤ M :=
  f.opNorm_le_bound hM h
-- BOOK: end op-norm

-- BOOK: begin op-comp
-- 合成の作用素ノルムは積で押さえられる
example (E F G : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : F →L[ℝ] G) (f : E →L[ℝ] F) : ‖g.comp f‖ ≤ ‖g‖ * ‖f‖ :=
  g.opNorm_comp_le f

-- 有界線形作用素は連続。有限次元と違い、これは条件である
example (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E →L[ℝ] F) : Continuous f :=
  f.continuous
-- BOOK: end op-comp

end Handbook.C34
