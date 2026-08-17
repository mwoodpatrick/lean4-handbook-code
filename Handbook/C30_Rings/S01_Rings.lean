/- 第30章 環論
   30.2 イデアル / 30.4 多項式環 / 30.5 PID・UFD -/
import Mathlib

namespace Handbook.C30

-- BOOK: begin ring-ideal
-- イデアル: 和で閉じ、環の任意の元を掛けても外に出ない
example (R : Type) [CommRing R] (I : Ideal R) (r x : R)
    (hx : x ∈ I) : r * x ∈ I :=
  I.mul_mem_left r hx

-- 剰余環はイデアルによる商
#check @Ideal.Quotient.mk
-- BOOK: end ring-ideal

-- BOOK: begin ring-hom
-- 環準同型 R →+* S は加法と乗法をともに保つ
example (R S : Type) [CommRing R] [CommRing S] (f : R →+* S)
    (a b : R) : f (a * b) = f a * f b :=
  f.map_mul a b

-- 第一同型定理: R/ker f ≅ im f(群論と同じ設計)
noncomputable example (R S : Type) [CommRing R] [CommRing S]
    (f : R →+* S) : (R ⧸ RingHom.ker f) ≃+* f.range :=
  RingHom.quotientKerEquivRange f
-- BOOK: end ring-hom

-- BOOK: begin polynomial
open Polynomial in
-- 多項式環 ℚ[X]。X は不定元。
example : (X + 1 : Polynomial ℚ) * (X - 1) = X ^ 2 - 1 := by
  ring
-- BOOK: end polynomial

-- BOOK: begin ufd
-- ℤ は単項イデアル整域(PID)であり、一意分解整域(UFD)
example : IsPrincipalIdealRing ℤ := inferInstance
example : UniqueFactorizationMonoid ℤ := inferInstance
-- BOOK: end ufd

-- BOOK: begin prime-maximal
-- 素イデアル: ab ∈ 𝔭 なら a ∈ 𝔭 または b ∈ 𝔭(素数の一般化)
example (R : Type) [CommRing R] (P : Ideal R) :
    P.IsPrime ↔ P ≠ ⊤ ∧ ∀ {x y : R}, x * y ∈ P → x ∈ P ∨ y ∈ P :=
  Ideal.isPrime_iff

-- 極大イデアル ⟺ 商が体
example (R : Type) [CommRing R] (I : Ideal R) :
    I.IsMaximal ↔ IsField (R ⧸ I) :=
  Ideal.Quotient.maximal_ideal_iff_isField_quotient I
-- BOOK: end prime-maximal

-- BOOK: begin crt
-- 中国剰余定理(ZMod 版): 互いに素なら剰余環が直積へ分解する
example (m n : ℕ) (h : m.Coprime n) :
    ZMod (m * n) ≃+* ZMod m × ZMod n :=
  ZMod.chineseRemainder h
-- BOOK: end crt

end Handbook.C30
