/- 第19章 微分
   19.8 微分の応用: 極値・逆関数・凸性 -/
import Mathlib

namespace Handbook.C19

-- BOOK: begin local-extr
-- Fermat の定理。極小点では導関数が消える
example (f : ℝ → ℝ) (a : ℝ) (h : IsLocalMin f a) :
    deriv f a = 0 :=
  h.deriv_eq_zero

-- 極大・極小をまとめた IsLocalExtr 版もある
#check @IsLocalExtr.deriv_eq_zero
-- BOOK: end local-extr

-- BOOK: begin rolle-search
-- ロルの定理の deriv 版。停留点の存在を与える
#check @exists_deriv_eq_zero
-- BOOK: end rolle-search

-- BOOK: begin inv-deriv
-- 逆関数の微分。log は exp の逆で、(log)' x = 1/x
example (x : ℝ) (hx : x ≠ 0) : HasDerivAt Real.log x⁻¹ x :=
  Real.hasDerivAt_log hx

-- 一般形。f' ≠ 0 が要る(接線が水平だと逆が微分できない)
#check @HasDerivAt.of_local_left_inverse
-- BOOK: end inv-deriv

-- BOOK: begin convex-deriv2
-- 2階微分が正なら狭義凸。x ↦ x² で確かめる
example : StrictConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) := by
  apply strictConvexOn_of_deriv2_pos convex_univ
  · fun_prop
  · intro x _
    simp
    norm_num
-- BOOK: end convex-deriv2

-- BOOK: begin contdiff-inf
-- exp は C^∞ 級。n : WithTop ℕ∞ なので任意の階数で成り立つ
#check @Real.contDiff_exp

-- C^∞ の特徴づけ: 微分可能かつ導関数がまた C^∞
#check @contDiff_infty_iff_deriv
-- BOOK: end contdiff-inf

end Handbook.C19
