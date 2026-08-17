/- 第39章 代数幾何入門
   39.3 スペクトルと Zariski 位相 -/
import Mathlib

namespace Handbook.C39

-- BOOK: begin spectrum
-- 環の素スペクトル: 素イデアル(第30章)を「点」とみなす空間
#check @PrimeSpectrum

-- Zariski 位相が入っている
example (R : Type) [CommRing R] :
    TopologicalSpace (PrimeSpectrum R) :=
  inferInstance
-- BOOK: end spectrum

-- BOOK: begin spec-int
-- Spec ℤ の点。素数 2 が生成する素イデアルが1つの点になる
example : PrimeSpectrum ℤ :=
  ⟨Ideal.span {2}, by
    rw [Ideal.span_singleton_prime (by norm_num)]
    exact Int.prime_two⟩

-- 零イデアルも素イデアル(ℤ が整域だから)。これが生成点
example : PrimeSpectrum ℤ :=
  ⟨⊥, Ideal.isPrime_bot⟩
-- BOOK: end spec-int

-- BOOK: begin prime-vs-maximal
-- 素イデアルの逆像は素イデアル。これが Spec を関手にする
example (R S : Type) [CommRing R] [CommRing S] (f : R →+* S)
    (p : Ideal S) [p.IsPrime] : (Ideal.comap f p).IsPrime := by
  infer_instance

-- 極大イデアルではこうならない。ℤ → ℚ で (0) は ℚ では極大だが
-- 逆像 (0) は ℤ では極大でない
example : Ideal.comap (Int.castRingHom ℚ) (⊥ : Ideal ℚ) = ⊥ := by
  ext x
  simp [Ideal.mem_comap]
-- BOOK: end prime-vs-maximal

-- BOOK: begin comap
-- 環の射 R →+* S が Spec S → Spec R を誘導する(向きが逆)
example (R S : Type) [CommRing R] [CommRing S] (f : R →+* S) :
    PrimeSpectrum S → PrimeSpectrum R :=
  PrimeSpectrum.comap f
-- BOOK: end comap

-- BOOK: begin basic-open
-- 基本開集合 D(f): f が消えない点の全体。Zariski 位相の基底になる
#check @PrimeSpectrum.basicOpen

-- 点の閉包は、その素イデアルの零点集合に等しい
example (R : Type) [CommRing R] (x : PrimeSpectrum R) :
    closure {x} = PrimeSpectrum.zeroLocus x.asIdeal :=
  PrimeSpectrum.closure_singleton x
-- BOOK: end basic-open

-- BOOK: begin zero-locus
-- 零点集合: イデアルを含む素イデアル全体。Zariski 閉集合の定義
#check @PrimeSpectrum.zeroLocus

-- 消滅イデアル。零点集合と対をなす
#check @PrimeSpectrum.vanishingIdeal
-- BOOK: end zero-locus

end Handbook.C39
