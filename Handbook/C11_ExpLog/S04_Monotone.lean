/- 第11章 指数関数と対数関数
   11.5 増減とグラフ -/
import Mathlib

namespace Handbook.C11

-- BOOK: begin exp-mono
-- exp は狭義単調増加、値はつねに正
example : StrictMono Real.exp := Real.exp_strictMono

example (x : ℝ) : 0 < Real.exp x := Real.exp_pos x
-- BOOK: end exp-mono

-- BOOK: begin log-mono
-- log は正の実数の上で狭義単調増加
example : StrictMonoOn Real.log (Set.Ioi 0) :=
  Real.strictMonoOn_log
-- BOOK: end log-mono

-- BOOK: begin exp-eq
-- 指数方程式・不等式は単射性・単調性で「指数比べ」に落ちる
example (x : ℝ) : Real.exp x = Real.exp 3 ↔ x = 3 :=
  Real.exp_eq_exp

example (x y : ℝ) : Real.exp x < Real.exp y ↔ x < y :=
  Real.exp_lt_exp
-- BOOK: end exp-eq

-- BOOK: begin exp-solve
-- 例題: e^(2x) = e^(x+1) を解く
example (x : ℝ) :
    Real.exp (2 * x) = Real.exp (x + 1) ↔ x = 1 := by
  rw [Real.exp_eq_exp]
  constructor
  · intro h; linarith
  · rintro rfl; norm_num
-- BOOK: end exp-solve

-- BOOK: begin log-solve
-- 対数の符号は「1 との大小」で決まる
example (x : ℝ) (hx : 0 < x) : Real.log x < 0 ↔ x < 1 :=
  Real.log_neg_iff hx

example (x : ℝ) (hx : 1 < x) : 0 < Real.log x :=
  Real.log_pos hx
-- BOOK: end log-solve

end Handbook.C11
