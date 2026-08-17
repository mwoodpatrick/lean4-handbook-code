/- 第17章 実数と数列の極限
   17.1 実数とは何か — 完備順序体 -/
import Mathlib

namespace Handbook.C17

-- BOOK: begin real-complete
-- ℝ の核心: 空でなく上に有界な集合は上限(最小上界)を持つ
example (S : Set ℝ) (hne : S.Nonempty) (hbdd : BddAbove S) :
    IsLUB S (sSup S) :=
  isLUB_csSup hne hbdd
-- BOOK: end real-complete

-- BOOK: begin real-sqrt2
-- だから √2 が「存在する」(ℚ には存在しなかった: 第6章)
example : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
-- BOOK: end real-sqrt2

-- BOOK: begin real-arch
-- アルキメデスの性質: どんな実数も超える自然数が取れる
example (x : ℝ) : ∃ n : ℕ, x < n := exists_nat_gt x

-- ℝ はアルキメデス的順序体(型クラスとして登録済み)
example : Archimedean ℝ := inferInstance
-- BOOK: end real-arch

-- BOOK: begin sup-le
-- 上限は「上界のうち最小」— 2つの補題がその両面を与える
example (S : Set ℝ) (x : ℝ) (hbdd : BddAbove S) (hx : x ∈ S) :
    x ≤ sSup S :=
  le_csSup hbdd hx

example (S : Set ℝ) (hne : S.Nonempty) (b : ℝ)
    (hb : ∀ x ∈ S, x ≤ b) : sSup S ≤ b :=
  csSup_le hne hb
-- BOOK: end sup-le

end Handbook.C17
