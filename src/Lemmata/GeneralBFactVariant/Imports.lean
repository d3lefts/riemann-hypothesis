module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

namespace Bl.general_b_fact_variant

theorem goal1 {n : ℕ} {N N' B B' : Matrix (Fin n) (Fin n) ℂ}
    (h1 : N.BlockTriangular OrderDual.toDual) (h2 : N'.BlockTriangular OrderDual.toDual)
    (h3 : ∀ i, N i i = 1) (h4 : ∀ i, N' i i = 1)
    (h5 : B.BlockTriangular id) (h6 : B'.BlockTriangular id)
    (h7 : B.det ≠ 0) (h8 : N * B = N' * B') :
    N = N' := by
  have hu : IsUnit N'.det := by simp [Matrix.det_of_isLowerTriangular N' h2, h4]
  have hB : IsUnit B.det := isUnit_iff_ne_zero.mpr h7
  let _ : Invertible N' := Matrix.invertibleOfIsUnitDet N' hu
  let _ : Invertible B := Matrix.invertibleOfIsUnitDet B hB
  set M := N'⁻¹ * N
  have hMe : M = B' * B⁻¹ := by
    calc M = N'⁻¹ * (N * B) * B⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv B hB, Matrix.mul_one]
      _ = B' * B⁻¹ := by
          rw [h8, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul N' hu, Matrix.one_mul]
  have hMl : M.BlockTriangular OrderDual.toDual :=
    (Matrix.blockTriangular_inv_of_blockTriangular h2).mul h1
  have hMu : M.BlockTriangular id :=
    hMe ▸ h6.mul (Matrix.blockTriangular_inv_of_blockTriangular h5)
  have hoff {i j} (hij : i ≠ j) : M i j = 0 :=
    (lt_or_gt_of_ne hij).elim (fun h => hMl h) fun h => hMu h
  have hNM : N = N' * M := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv N' hu, Matrix.one_mul]
  have hM1 : M = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      have h := congrFun (congrFun hNM i) i
      rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => by rw [hoff hk, mul_zero])
        (fun h => absurd (Finset.mem_univ i) h), h3, h4, one_mul] at h
      rw [← h, Matrix.one_apply_eq]
    · rw [hoff hij, Matrix.one_apply_ne hij]
  rw [hNM, hM1, Matrix.mul_one]

end Bl.general_b_fact_variant
