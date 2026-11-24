module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

namespace Bl.general_b_fact_form

theorem goal1 {n : ℕ} {N N' U U' : Matrix (Fin n) (Fin n) ℂ}
    (hN : N.BlockTriangular OrderDual.toDual) (hNd : ∀ a, N a a = 1)
    (hN' : N'.BlockTriangular OrderDual.toDual) (hN'd : ∀ a, N' a a = 1)
    (hU : U.BlockTriangular id) (hU' : U'.BlockTriangular id)
    (hdet : U'.det ≠ 0) (hEq : N * U = N' * U') :
    N = N' ∧ U = U' := by
  have hdN : N.det = 1 := by simp [Matrix.det_of_isLowerTriangular N hN, hNd]
  have hdN' : N'.det = 1 := by simp [Matrix.det_of_isLowerTriangular N' hN', hN'd]
  have uN : IsUnit N.det := hdN ▸ isUnit_one
  have uN' : IsUnit N'.det := hdN' ▸ isUnit_one
  have uU : IsUnit U.det := isUnit_iff_ne_zero.mpr <| by
    have h := congrArg Matrix.det hEq
    simp only [Matrix.det_mul, hdN, hdN', one_mul] at h
    exact h ▸ hdet
  let _ : Invertible N' := Matrix.invertibleOfIsUnitDet N' uN'
  let _ : Invertible U := Matrix.invertibleOfIsUnitDet U uU
  have hAeq : N'⁻¹ * N = U' * U⁻¹ := by
    calc N'⁻¹ * N = N'⁻¹ * (N * U) * U⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv U uU, Matrix.mul_one]
      _ = U' * U⁻¹ := by
          rw [hEq, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul N' uN', Matrix.one_mul]
  have hAl : (N'⁻¹ * N).BlockTriangular OrderDual.toDual :=
    (Matrix.blockTriangular_inv_of_blockTriangular hN').mul hN
  have hAu : (N'⁻¹ * N).BlockTriangular id :=
    hAeq ▸ hU'.mul (Matrix.blockTriangular_inv_of_blockTriangular hU)
  have hoff {i j} (hij : i ≠ j) : (N'⁻¹ * N) i j = 0 :=
    (lt_or_gt_of_ne hij).elim (fun h => hAl (OrderDual.toDual_lt_toDual.mpr h)) fun h => hAu h
  have hNA : N = N' * (N'⁻¹ * N) := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv N' uN', Matrix.one_mul]
  have hA1 : N'⁻¹ * N = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      have h1 := congrFun (congrFun hNA i) i
      rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => by rw [hoff hk, mul_zero])
        (fun h => absurd (Finset.mem_univ i) h), hNd, hN'd, one_mul] at h1
      rw [← h1, Matrix.one_apply_eq]
    · rw [hoff hij, Matrix.one_apply_ne hij]
  have hNN : N = N' := by rw [hNA, hA1, Matrix.mul_one]
  exact ⟨hNN, by
    calc U = N⁻¹ * (N * U) := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul N uN, Matrix.one_mul]
      _ = U' := by rw [hEq, hNN, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul N' uN', Matrix.one_mul]⟩

end Bl.general_b_fact_form
