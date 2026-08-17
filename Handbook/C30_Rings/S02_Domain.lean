/- 第30章 環論
   30.2 整域と体 / 30.6 既約元と素元 -/
import Mathlib

namespace Handbook.C30

-- BOOK: begin domain-zero-divisor
-- ℤ/6 は整域でない。2·3 = 0 だが 2 ≠ 0, 3 ≠ 0
example : (2 : ZMod 6) * 3 = 0 := by decide

-- 素数を法とすれば体になる。零因子が消える
example (p : ℕ) [Fact p.Prime] : Field (ZMod p) := inferInstance
-- BOOK: end domain-zero-divisor

-- BOOK: begin domain-cancel
-- 整域では消去律が使える。零因子がないことの言い換えである
example (R : Type) [CommRing R] [IsDomain R] (a b c : R)
    (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
  mul_left_cancel₀ ha h
-- BOOK: end domain-cancel

-- BOOK: begin irreducible-prime
-- 既約元(それ以上分解できない)と素元(積を割れば因子を割る)
#check @Irreducible
#check @Prime

-- 一意分解整域では両者が一致する。
-- 一般の環では「既約だが素でない」元が存在しうる
#check @UniqueFactorizationMonoid.irreducible_iff_prime
-- BOOK: end irreducible-prime

-- BOOK: begin maximal-exists
-- 単位的な環には必ず極大イデアルがある(Zorn の補題を使う)
#check @Ideal.exists_maximal
-- BOOK: end maximal-exists

end Handbook.C30
