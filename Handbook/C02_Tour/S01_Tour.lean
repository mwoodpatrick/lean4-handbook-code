/- 第2章 Lean 4 ツアー
   定義や文法の説明は後回しにして、Lean が数学を検証する様子を見せる。 -/
import Mathlib

namespace Handbook.C02

-- BOOK: begin tour-one-one
-- 1 + 1 = 2。数学の全景はここから始まる。
example : 1 + 1 = 2 := by norm_num

-- 証明は「計算で確かめられる」こともあれば、
-- 定義から直ちに従う(rfl)こともある。
example : 1 + 1 = 2 := rfl
-- BOOK: end tour-one-one

-- BOOK: begin tour-false
-- 偽の主張は証明できない。「等しくない」も定理である。
example : 1 + 1 ≠ 3 := by decide
-- BOOK: end tour-false

-- BOOK: begin tour-compute
-- Lean は証明支援系であると同時に、電卓でもある。
#eval 2 ^ 100
-- 出力: 1267650600228229401496703205376

#eval Nat.factorial 20  -- 出力: 2432902008176640000
-- BOOK: end tour-compute

-- BOOK: begin tour-compute2
-- 分数は正確に、リストは丸ごと計算できる
#eval (1 / 3 + 1 / 6 : ℚ)          -- 出力: 1/2
#eval (List.range 10).map (2 ^ ·)  -- 2 の冪の一覧
#eval Nat.minFac 91                -- 出力: 7(最小の素因数)
-- BOOK: end tour-compute2

-- BOOK: begin tour-sqrt2
-- 「2の平方根は無理数である」。古代ギリシアの大定理が1行で引ける。
example : Irrational (Real.sqrt 2) := irrational_sqrt_two
-- BOOK: end tour-sqrt2

-- BOOK: begin tour-bignum
-- 多倍長計算は反例の道具。メルセンヌが素数と主張した 2⁶⁷ − 1 は
-- 合成数だった(コール、1903年)。
#eval 2 ^ 67 - 1  -- 出力: 147573952589676412927

example : 2 ^ 67 - 1 = 193707721 * 761838257287 := by
  norm_num
-- BOOK: end tour-bignum

-- BOOK: begin tour-sqrt2-approx
-- 近似の挟み撃ちも定理: 1.414² < 2 < 1.415²
example : (1.414 : ℚ) ^ 2 < 2 ∧ 2 < (1.415 : ℚ) ^ 2 := by
  constructor <;> norm_num
-- BOOK: end tour-sqrt2-approx

-- BOOK: begin tour-sqrt-gen
-- 一般化も1行。どんな素数の平方根も無理数である。
example : Irrational (Real.sqrt 3) :=
  Nat.prime_three.irrational_sqrt

example (p : ℕ) (hp : p.Prime) : Irrational (Real.sqrt p) :=
  hp.irrational_sqrt
-- BOOK: end tour-sqrt-gen

-- BOOK: begin tour-primes
-- 「素数は無限に存在する」。ユークリッドの定理。
-- 任意の n に対して、n 以上の素数 p が存在する。
example (n : ℕ) : ∃ p, n ≤ p ∧ p.Prime :=
  Nat.exists_infinite_primes n
-- BOOK: end tour-primes

-- BOOK: begin tour-primes-count
-- 100 未満の素数はちょうど 25 個ある(数えるのも証明も機械)
#eval ((Finset.range 100).filter Nat.Prime).card  -- 出力: 25

example : ((Finset.range 100).filter Nat.Prime).card = 25 := by
  decide
-- BOOK: end tour-primes-count

-- BOOK: begin tour-deriv
-- 微分も定理として計算できる。x² の x = 3 における微分係数は 6。
example : deriv (fun x : ℝ => x ^ 2) 3 = 6 := by
  norm_num [deriv_pow]

-- sin の微分は cos。解析学の定理も1行で引ける。
example : deriv Real.sin = Real.cos := Real.deriv_sin

-- 指数関数の 0 での傾きは 1(e の定義の心臓部)
example : deriv Real.exp 0 = 1 := by
  simp [Real.deriv_exp]
-- BOOK: end tour-deriv

-- BOOK: begin tour-decide
-- 有限の主張は decide が全数検査で片付ける。
-- 97 は素数、91 は素数でない(91 = 7 × 13)。
example : Nat.Prime 97 := by decide
example : ¬ Nat.Prime 91 := by decide
-- BOOK: end tour-decide

-- BOOK: begin tour-deriv-min
-- 微分の使い道の先取り: x² − 6x + 13 の最小値は 4(x = 3 で達成)
example (x : ℝ) : 4 ≤ x ^ 2 - 6 * x + 13 := by
  nlinarith [sq_nonneg (x - 3)]

example : (3 : ℝ) ^ 2 - 6 * 3 + 13 = 4 := by norm_num
-- BOOK: end tour-deriv-min

-- BOOK: begin tour-limit
-- 極限も定理である: 1/n → 0(第17章)
example :
    Filter.Tendsto (fun n : ℕ => (1 : ℝ) / n)
      Filter.atTop (nhds 0) :=
  tendsto_one_div_atTop_nhds_zero_nat

-- 無限級数も: 1 + 1/2 + 1/4 + … = 2(第21章)
example : ∑' n : ℕ, (1 / 2 : ℝ) ^ n = 2 := tsum_geometric_two
-- BOOK: end tour-limit

-- BOOK: begin tour-algebra
-- 展開・因数分解は ring に一任する(第6章)
example (x y : ℚ) : (x + y) * (x - y) = x ^ 2 - y ^ 2 := by
  ring

-- 12時間時計の世界では 7 + 8 = 3(合同式、第14章)
example : (7 : ZMod 12) + 8 = 3 := by decide
-- BOOK: end tour-algebra

-- BOOK: begin tour-dice
-- 2個のさいころの和が 7 になる確率は 6/36 = 1/6(第13章)
-- (目を 0..5 で持つので、和 7 は内部表現では和 5)
#eval ((Finset.range 6) ×ˢ (Finset.range 6)).card  -- 出力: 36
#eval (((Finset.range 6) ×ˢ (Finset.range 6)).filter
        (fun p => p.1 + p.2 = 5)).card             -- 出力: 6
-- BOOK: end tour-dice

-- BOOK: begin tour-det
-- 行列式も1行(線形代数、第23章)
example : (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℤ).det = -2 := by
  rw [Matrix.det_fin_two_of]
  norm_num
-- BOOK: end tour-det

-- BOOK: begin tour-exercises
-- 練習: 本章に登場した道具だけで検証できる3問
example : 2 ^ 10 = 1024 := by norm_num
example : Nat.gcd 111 74 = 37 := by decide
example : (5 : ZMod 12) + 9 = 2 := by decide
-- BOOK: end tour-exercises

-- BOOK: begin tour-error
/- 誤った証明を提出してみる:

  example : 1 + 1 = 3 := rfl

Lean の返答(エラーメッセージ):

  type mismatch
    rfl
  has type
    ?a = ?a : Prop
  but is expected to have type
    1 + 1 = 3 : Prop

「rfl の型(両辺が同じ形の等式)と、
 要求された型 1 + 1 = 3 が一致しない」という却下通知である。
-/
-- BOOK: end tour-error

-- BOOK: begin tour-error2
/- 頻出エラーその2。名前の打ち間違い:

  example (a b : ℕ) : a.gcd b ∣ a := Nat.gcd_dvd_lef a b

Lean の返答:

  unknown constant 'Nat.gcd_dvd_lef'

「そんな名前の宣言は存在しない」という通知である。
正しくは Nat.gcd_dvd_left(末尾の t が欠けていた)。
-/
-- BOOK: end tour-error2

-- BOOK: begin tour-imo
-- IMO 1959 第1問: (21n+4)/(14n+3) はすべての n で既約である。
theorem imo1959_p1 (n : ℕ) :
    Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
  have h := Nat.dvd_sub
    ((Nat.gcd_dvd_right (21 * n + 4) (14 * n + 3)).mul_left 3)
    ((Nat.gcd_dvd_left (21 * n + 4) (14 * n + 3)).mul_left 2)
  have e : 3 * (14 * n + 3) - 2 * (21 * n + 4) = 1 := by omega
  rw [e] at h
  exact Nat.dvd_one.mp h
-- BOOK: end tour-imo

end Handbook.C02
