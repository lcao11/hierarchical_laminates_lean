module

public import HierarchicalLaminates.Corrector.CellIdentification
public import HierarchicalLaminates.Homogenization.EffectiveBlocks

/-!
# The full effective tensor and symmetry of the reduced response

The corrector formula identifies the effective operator on every horizontal
loading. The vertical columns are fixed by the constituents. Together these
identities recover the entire effective matrix as the material tensor of the
mean reduced response.

Symmetry of the full tensor then implies symmetry of its reduced parameter:
the factor in the horizontal block has a left inverse obtained from its Gram
matrix. This recovers the reduced matrix itself from the symmetric lifted block.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.Corrector

open Matrix Periodic Material Lamination Homogenization

/-- The full effective matrix of the smooth phase arrangement is the material
tensor associated with its mean reduced response. -/
theorem smooth_effectiveMatrix_eq_materialTensor :
    effectiveMatrix smoothFraction = materialTensor meanResponseMatrix := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases j
  · let z : PotentialVector := WithLp.toLp 2 (Pi.single b (1 : ℝ))
    have hs : (horizontalLoading z : PhysicalIndex → ℝ) = Pi.single (0, b) 1 := by
      ext ⟨k, c⟩
      fin_cases k <;> simp [horizontalLoading, z, Pi.single_apply]
    have h := congrArg (fun F : PhysicalGradient => F (i, a)) (effective_horizontal_operator z)
    rw [← effectiveMatrix_operator] at h
    change (effectiveMatrix smoothFraction *ᵥ (horizontalLoading z : PhysicalIndex → ℝ)) (i, a) =
      (materialTensor meanResponseMatrix *ᵥ (horizontalLoading z : PhysicalIndex → ℝ)) (i, a) at h
    rw [hs] at h
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h
  · change effectiveMatrix smoothFraction (i, a) (1, b) =
      materialTensor meanResponseMatrix (i, a) (1, b)
    rw [effectiveMatrix_vertical_column]
    fin_cases i <;> simp [phaseZero, materialTensor]

/-- Symmetry of the material tensor implies symmetry of its reduced parameter,
using the explicit left inverse of the horizontal factor. -/
theorem materialTensor_reduced_isHermitian (H : RMatrix8)
    (hB : (materialTensor H).IsHermitian) : H.IsHermitian := by
  let P := factorR
  let Q := P * H * Pᵀ
  have hA : (horizontalR H).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro a b
    simpa [materialTensor] using hB.apply (0, a) (0, b)
  have hQ : Q.IsHermitian := by
    have h := Matrix.isHermitian_one.sub hA
    convert h using 1
    simp [Q, P, horizontalR]
  let L := gramInvR * Pᵀ
  have hLP : L * P = 1 := by
    dsimp [L, P]
    rw [Matrix.mul_assoc, factorR_gram, gramInvR_mul]
  have hrecover : L * Q * Lᵀ = H := by
    dsimp [Q]
    calc
      L * (P * H * Pᵀ) * Lᵀ = (L * P) * H * (L * P)ᵀ := by
        simp only [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
      _ = H := by rw [hLP]; simp
  change H.IsHermitian
  rw [← hrecover]
  have h := Matrix.isHermitian_mul_mul_conjTranspose L hQ
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using h

/-- The mean reduced response is symmetric because its full effective tensor is symmetric. -/
theorem meanResponseMatrix_isHermitian : meanResponseMatrix.IsHermitian := by
  apply materialTensor_reduced_isHermitian
  rw [← smooth_effectiveMatrix_eq_materialTensor]
  exact effectiveMatrix_isHermitian smoothFraction

end HierarchicalLaminates.Corrector
