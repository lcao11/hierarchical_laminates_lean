module

public import HierarchicalLaminates.Algebra.ParameterSpace

/-!
# The selected loading energies

The identities compare the two prescribed loading energies for every real
reduced parameter.
-/

@[expose] public section

namespace HierarchicalLaminates

open scoped Matrix

noncomputable section

def horizontalR (H : RMatrix8) : Matrix (Fin 16) (Fin 16) ℝ :=
  1 - factorR * H * factorRᵀ

theorem factorR_quadratic (H : RMatrix8) (v : Fin 16 → ℝ) :
    v ⬝ᵥ ((factorR * H * factorRᵀ) *ᵥ v) =
      (factorRᵀ *ᵥ v) ⬝ᵥ (H *ᵥ (factorRᵀ *ᵥ v)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

theorem horizontalR_quadratic (H : RMatrix8) (v : Fin 16 → ℝ) :
    v ⬝ᵥ (horizontalR H *ᵥ v) =
      v ⬝ᵥ v - (factorRᵀ *ᵥ v) ⬝ᵥ (H *ᵥ (factorRᵀ *ᵥ v)) := by
  rw [horizontalR, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub,
    factorR_quadratic]

theorem unitPlusR_quadratic (H : RMatrix8) : unitPlusR ⬝ᵥ (H *ᵥ unitPlusR) = H 0 0 := by
  simp [unitPlusR, realVector, unitPlusQ, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem unitMinusR_quadratic (H : RMatrix8) : unitMinusR ⬝ᵥ (H *ᵥ unitMinusR) = H 4 4 := by
  simp [unitMinusR, realVector, unitMinusQ, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem loadPlusR_energy (H : RMatrix8) :
    loadPlusR ⬝ᵥ (horizontalR H *ᵥ loadPlusR) = 4 / 3 - H 0 0 := by
  rw [horizontalR_quadratic, factorR_loadPlus, unitPlusR_quadratic]
  have hnorm : loadPlusR ⬝ᵥ loadPlusR = 4 / 3 := loadPlusR_sq
  rw [hnorm]

theorem loadMinusR_energy (H : RMatrix8) :
    loadMinusR ⬝ᵥ (horizontalR H *ᵥ loadMinusR) = 4 / 3 - H 4 4 := by
  rw [horizontalR_quadratic, factorR_loadMinus, unitMinusR_quadratic]
  have hnorm : loadMinusR ⬝ᵥ loadMinusR = 4 / 3 := loadMinusR_sq
  rw [hnorm]

def horizontalDifferenceR (H : RMatrix8) : ℝ :=
  loadMinusR ⬝ᵥ (horizontalR H *ᵥ loadMinusR) -
    loadPlusR ⬝ᵥ (horizontalR H *ᵥ loadPlusR)

theorem horizontalDifferenceR_eq (H : RMatrix8) :
    horizontalDifferenceR H = reducedDifferenceR H := by
  rw [horizontalDifferenceR, loadMinusR_energy, loadPlusR_energy, reducedDifferenceR]
  ring

theorem horizontalDifferenceR_zero_of_spinMember {H : RMatrix8} (hH : SpinMember H) :
    horizontalDifferenceR H = 0 := by
  rw [horizontalDifferenceR_eq]
  exact reducedDifferenceR_zero_of_spinMember hH

end

end HierarchicalLaminates
