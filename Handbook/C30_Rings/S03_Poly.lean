/- 第30章 環論
   30.4 多項式環 -/
import Mathlib

namespace Handbook.C30

open Polynomial

-- BOOK: begin poly-degree
-- 次数は WithBot ℕ。零多項式の次数を ⊥ にするための設計
#check @Polynomial.degree

-- 整域上では積の次数が次数の和になる
example (R : Type) [CommRing R] [IsDomain R] (p q : R[X]) :
    (p * q).degree = p.degree + q.degree :=
  degree_mul
-- BOOK: end poly-degree

-- BOOK: begin poly-factor
-- 因数定理: a が根であることと X - a で割れることは同値
example (R : Type) [CommRing R] (p : R[X]) (a : R) :
    (X - C a) ∣ p ↔ p.IsRoot a :=
  dvd_iff_isRoot
-- BOOK: end poly-factor

-- BOOK: begin poly-euclid
-- 体上の多項式環はユークリッド整域。割り算ができる
noncomputable example (K : Type) [Field K] :
    EuclideanDomain K[X] :=
  inferInstance

-- ゆえに単項イデアル整域でもある
example (K : Type) [Field K] : IsPrincipalIdealRing K[X] :=
  inferInstance
-- BOOK: end poly-euclid

-- BOOK: begin poly-noetherian
-- Hilbert の基底定理: Noether 環の多項式環も Noether 環
#check @Polynomial.isNoetherianRing
-- BOOK: end poly-noetherian

end Handbook.C30
