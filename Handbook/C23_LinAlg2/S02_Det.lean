/- 第23章 線形代数II — 行列・行列式・固有値
   23.3 行列式 / 23.4 固有値 -/
import Mathlib

namespace Handbook.C23

-- BOOK: begin det
-- 2次の行列式 ad - bc
example : (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℚ).det = -2 := by
  rw [Matrix.det_fin_two_of]
  norm_num

-- 行列式の乗法性
example (M N : Matrix (Fin 2) (Fin 2) ℚ) :
    (M * N).det = M.det * N.det :=
  Matrix.det_mul M N
-- BOOK: end det

-- BOOK: begin det-props
-- 単位行列の行列式は 1(体積を変えない)
example : (1 : Matrix (Fin 2) (Fin 2) ℚ).det = 1 := Matrix.det_one

-- 転置しても行列式は変わらない
example (M : Matrix (Fin 2) (Fin 2) ℚ) : M.transpose.det = M.det :=
  Matrix.det_transpose M
-- BOOK: end det-props

-- BOOK: begin inverse
-- 行列式が可逆なら逆行列が存在する
example (M : Matrix (Fin 2) (Fin 2) ℚ) (h : IsUnit M.det) :
    M * M⁻¹ = 1 :=
  Matrix.mul_nonsing_inv M h

-- 固有値の一般論は Module.End(線形変換)の言葉で
#check @Module.End.HasEigenvalue
-- BOOK: end inverse

-- BOOK: begin eigen-def
-- 固有ベクトル: T v = μ v(向きが変わらず倍率 μ だけ変わる、v ≠ 0)
-- HasEigenvector μ v は「μ が固有値で v がその固有ベクトル」
example {V : Type} [AddCommGroup V] [Module ℝ V]
    (T : Module.End ℝ V) (μ : ℝ) (v : V)
    (h : T.HasEigenvector μ v) : T v = μ • v :=
  h.apply_eq_smul
-- BOOK: end eigen-def

end Handbook.C23
