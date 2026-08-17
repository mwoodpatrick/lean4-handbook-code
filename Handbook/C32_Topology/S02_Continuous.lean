/- 第32章 位相空間論
   32.2 連続写像と同相 -/
import Mathlib

namespace Handbook.C32

-- BOOK: begin cont-def
-- 連続の定義: 開集合の逆像が開(第16章の逆像がここで主役に)
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) :
    Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s) :=
  continuous_def

-- 閉集合版も同値。開でも閉でも同じ連続性が定まる
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) :
    Continuous f ↔ ∀ s, IsClosed s → IsClosed (f ⁻¹' s) :=
  continuous_iff_isClosed
-- BOOK: end cont-def

-- BOOK: begin cont-comp
-- 恒等写像と定値写像は連続、連続の合成は連続
example (X : Type) [TopologicalSpace X] : Continuous (id : X → X) :=
  continuous_id

example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (y : Y) : Continuous (fun _ : X => y) :=
  continuous_const

example (X Y Z : Type) [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : X → Y) (g : Y → Z)
    (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) :=
  hg.comp hf
-- BOOK: end cont-comp

-- BOOK: begin homeomorph
-- 同相 ≃ₜ は「連続な全単射で逆も連続」— 位相的な同一視
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) : Continuous e ∧ Continuous e.symm :=
  ⟨e.continuous, e.symm.continuous⟩

-- 同相なら開集合が1対1に対応する
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (s : Set Y) (hs : IsOpen s) : IsOpen (e ⁻¹' s) :=
  hs.preimage e.continuous
-- BOOK: end homeomorph

end Handbook.C32
