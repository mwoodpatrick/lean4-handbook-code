/- 第36章 多様体
   36.4 多様体間の滑らかな写像 -/
import Mathlib

namespace Handbook.C36

open Manifold

/-- 記述を短くするための自明モデル(ℝ 上の1次元) -/
noncomputable abbrev I1 : ModelWithCorners ℝ ℝ ℝ := modelWithCornersSelf ℝ ℝ

-- BOOK: begin smooth-basic
-- 恒等写像は滑らか。ContMDiff の第3引数が微分可能性の階数
example : ContMDiff I1 I1 ⊤ (id : ℝ → ℝ) :=
  contMDiff_id

-- 定値写像も滑らか
example (c : ℝ) : ContMDiff I1 I1 ⊤ (fun _ : ℝ => c) :=
  contMDiff_const
-- BOOK: end smooth-basic

-- BOOK: begin smooth-comp
-- 滑らかな写像の合成は滑らか
example (f g : ℝ → ℝ) (hf : ContMDiff I1 I1 ⊤ f)
    (hg : ContMDiff I1 I1 ⊤ g) : ContMDiff I1 I1 ⊤ (g ∘ f) :=
  hg.comp hf

-- 滑らかならば連続(第32章の位相へ戻る)
example (f : ℝ → ℝ) (hf : ContMDiff I1 I1 ⊤ f) : Continuous f :=
  hf.continuous
-- BOOK: end smooth-comp

end Handbook.C36
