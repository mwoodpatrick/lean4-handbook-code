/- 第24章 多変数の微積分
   24.7 逆関数定理と陰関数定理 -/
import Mathlib

namespace Handbook.C24

-- BOOK: begin inverse-strict
-- 逆関数定理が要求するのは HasFDerivAt より強い条件
#check @HasStrictFDerivAt

-- C¹ 級なら強い意味の全微分が自動的に従う
#check @ContDiffAt.hasStrictFDerivAt
-- BOOK: end inverse-strict

-- BOOK: begin inverse-local
-- 微分が可逆(≃L)なら、局所逆写像が構成できる
#check @HasStrictFDerivAt.localInverse

-- その局所逆写像は、点 a の近くで本当に左逆になっている
example (f : ℝ × ℝ → ℝ × ℝ) (f' : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (a : ℝ × ℝ) (hf : HasStrictFDerivAt f (f' : ℝ × ℝ →L[ℝ] ℝ × ℝ) a) :
    ∀ᶠ x in nhds a, hf.localInverse f f' a (f x) = x :=
  hf.eventually_left_inverse
-- BOOK: end inverse-local

-- BOOK: begin inverse-deriv
-- 逆写像の全微分は、元の微分の逆写像である
example (f : ℝ × ℝ → ℝ × ℝ) (f' : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (a : ℝ × ℝ) (hf : HasStrictFDerivAt f (f' : ℝ × ℝ →L[ℝ] ℝ × ℝ) a) :
    HasStrictFDerivAt (hf.localInverse f f' a)
      (f'.symm : ℝ × ℝ →L[ℝ] ℝ × ℝ) (f a) :=
  hf.to_localInverse
-- BOOK: end inverse-deriv

-- BOOK: begin implicit-data
-- 陰関数定理は、この構造体を組み立てて使う
#check @ImplicitFunctionData
-- BOOK: end implicit-data

end Handbook.C24
