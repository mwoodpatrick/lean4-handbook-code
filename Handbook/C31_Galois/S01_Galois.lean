/- 第31章 体論とガロア理論
   31.1 体と拡大体 / 31.5 Galois 対応 / 31.6 Abel–Ruffini -/
import Mathlib

namespace Handbook.C31

-- BOOK: begin field-ext
-- 体の拡大の次数: ℂ は ℝ 上 2 次元
example : Module.finrank ℝ ℂ = 2 :=
  Complex.finrank_real_complex

-- 中間体(拡大の途中にある体)
#check @IntermediateField
-- BOOK: end field-ext

-- BOOK: begin minpoly
-- 最小多項式: α はその根であり、最小多項式は既約
example (K L : Type) [Field K] [Field L] [Algebra K L] (α : L) :
    (Polynomial.aeval α) (minpoly K α) = 0 :=
  minpoly.aeval K α

example (K L : Type) [Field K] [Field L] [Algebra K L] (α : L)
    (h : IsIntegral K α) : Irreducible (minpoly K α) :=
  minpoly.irreducible h
-- BOOK: end minpoly

-- BOOK: begin galois
-- ガロア拡大とガロア対応(中間体と部分群の逆転対応)
#check @IsGalois
#check @IsGalois.intermediateFieldEquivSubgroup
-- BOOK: end galois

-- BOOK: begin abel-ruffini
-- Abel–Ruffini の核心: 冪根で書ける元 x では、その最小多項式の
-- ガロア群は可解になる。対偶で「非可解 ⇒ 冪根で書けない」。
example (F E : Type) [Field F] [Field E] [Algebra F E]
    (x : E) (hx : x ∈ solvableByRad F E) :
    IsSolvable (minpoly F x).Gal :=
  isSolvable_gal_minpoly hx
-- BOOK: end abel-ruffini

end Handbook.C31
