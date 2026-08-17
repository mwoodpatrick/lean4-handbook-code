/- 第15章 ベクトル
   15.4 空間ベクトルと外積 -/
import Mathlib

namespace Handbook.C15

open scoped Matrix

-- BOOK: begin dot-eval
-- 内積の成分計算: (1,2)·(3,-1) = 1·3 + 2·(-1) = 1
#eval (![1, 2] : Fin 2 → ℤ) ⬝ᵥ ![3, -1]  -- 出力: 1
-- BOOK: end dot-eval

-- BOOK: begin vec-components
-- 成分計算: 和とスカラー倍は成分ごと(List にして表示)
#eval List.ofFn ((![1, 2] : Fin 2 → ℤ) + ![3, 4])
-- 出力: [4, 6]
#eval List.ofFn ((3 : ℤ) • (![1, 2] : Fin 2 → ℤ))
-- 出力: [3, 6]

-- 成分ごとの等式は decide でも閉じる
example : (![1, 2] : Fin 2 → ℤ) + ![3, 4] = ![4, 6] := by
  decide
-- BOOK: end vec-components

-- BOOK: begin vec-area
-- 2次元では行列式が「符号付き面積」を与える
-- (3,1) と (2,5) の張る平行四辺形の面積は 3·5 − 1·2 = 13
example :
    (!![3, 1; 2, 5] : Matrix (Fin 2) (Fin 2) ℤ).det = 13 := by
  rw [Matrix.det_fin_two_of]
  norm_num
-- BOOK: end vec-area

-- BOOK: begin vec-cross
-- 外積(3次元)。反交換的で、自身との外積は 0。
example (u v : Fin 3 → ℝ) : -(u ⨯₃ v) = v ⨯₃ u :=
  cross_anticomm u v

example (u : Fin 3 → ℝ) : u ⨯₃ u = 0 :=
  cross_self u
-- BOOK: end vec-cross

-- BOOK: begin vec-cross-dot
-- 外積は元の2本と直交する(スカラー三重積が 0)
example (u v : Fin 3 → ℝ) : u ⬝ᵥ u ⨯₃ v = 0 :=
  dot_self_cross u v
-- BOOK: end vec-cross-dot

-- BOOK: begin vec-perp-solve
-- 例題: (x, 6) が (1, 2) と直交する x を確定する
example (x : ℚ) :
    (![x, 6] : Fin 2 → ℚ) ⬝ᵥ ![1, 2] = 0 ↔ x = -12 := by
  simp only [dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · intro h; linarith
  · rintro rfl; norm_num
-- BOOK: end vec-perp-solve

-- BOOK: begin vec-section
-- 2:1 の内分点: P = (1/3)a + (2/3)b の成分計算
#eval List.ofFn (((1 : ℚ)/3) • (![0, 0] : Fin 2 → ℚ)
  + ((2 : ℚ)/3) • ![6, 3])
-- 出力: [4, 2]
-- BOOK: end vec-section

-- BOOK: begin vectors-exercises
-- 演習: 直交の判定・ノルムの斉次性
example : (![1, 2] : Fin 2 → ℤ) ⬝ᵥ ![2, -1] = 0 := by decide

example (x : EuclideanSpace ℝ (Fin 2)) :
    ‖(2 : ℝ) • x‖ = 2 * ‖x‖ := by
  rw [norm_smul, Real.norm_eq_abs]
  norm_num
-- BOOK: end vectors-exercises

end Handbook.C15
