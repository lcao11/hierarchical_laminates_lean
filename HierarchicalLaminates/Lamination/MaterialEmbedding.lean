module

public import HierarchicalLaminates.Lamination.ConstitutiveFamily

/-!
# The reduced parameter embedded in the full physical tensor
-/

@[expose] public section

namespace HierarchicalLaminates.Lamination

open Matrix

noncomputable section

def reducedLiftMatrix : Matrix (Fin 2 × Fin 16) (Fin 8) ℝ :=
  Matrix.of fun i j => if i.1 = 0 then factorR i.2 j else 0

theorem materialTensor_affine (H : RMatrix8) :
    materialTensor H = phaseZero - reducedLiftMatrix * H * reducedLiftMatrixᵀ := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases j <;>
    simp [materialTensor, phaseZero, horizontalR, reducedLiftMatrix,
      Matrix.mul_apply, Matrix.transpose_apply]

theorem normalMatrix_reducedLift (n : LayerNormal) :
    (normalMatrix n)ᵀ * reducedLiftMatrix = n.coordinates 0 • factorR := by
  ext a b
  simp [Matrix.mul_apply, normalMatrix, reducedLiftMatrix, Matrix.transpose_apply,
    Fintype.sum_prod_type, Pi.single_apply]

theorem jumpSourceMatrix_material (H₁ H₂ : RMatrix8) (n : LayerNormal) :
    jumpSourceMatrix (materialTensor H₁) (materialTensor H₂) n =
      n.coordinates 0 • (factorR * (H₁ - H₂) * reducedLiftMatrixᵀ) := by
  unfold jumpSourceMatrix
  rw [materialTensor_affine, materialTensor_affine]
  have hdiff : phaseZero - reducedLiftMatrix * H₂ * reducedLiftMatrixᵀ -
      (phaseZero - reducedLiftMatrix * H₁ * reducedLiftMatrixᵀ) =
      reducedLiftMatrix * (H₁ - H₂) * reducedLiftMatrixᵀ := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    abel
  rw [hdiff]
  simp only [← Matrix.mul_assoc, normalMatrix_reducedLift, Matrix.smul_mul]

theorem materialTensor_schur_correction (H Δ : RMatrix8) (hΔ : Δ.IsHermitian)
    (R : Matrix (Fin 16) (Fin 16) ℝ) (a nx : ℝ) :
    materialTensor H - a •
      ((nx • (factorR * Δ * reducedLiftMatrixᵀ))ᵀ * R *
        (nx • (factorR * Δ * reducedLiftMatrixᵀ))) =
      materialTensor (H + a • (Δ * (nx ^ 2 • (factorRᵀ * R * factorR)) * Δ)) := by
  have htranspose : Δᵀ = Δ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hΔ.eq
  rw [materialTensor_affine, materialTensor_affine]
  simp only [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose,
    htranspose, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_assoc, smul_smul]
  module

end

end HierarchicalLaminates.Lamination
