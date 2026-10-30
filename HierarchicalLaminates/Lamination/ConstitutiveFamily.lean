module

public import HierarchicalLaminates.Algebra.Loadings
public import HierarchicalLaminates.Algebra.Positivity
public import HierarchicalLaminates.Lamination.Separation
public import HierarchicalLaminates.Lamination.SpatialBlocks
public import Mathlib.Tactic.Module

/-!
# The constitutive family on sixteen potentials

The flattened gradient index is `(spatial direction, scalar potential)`.
An `8 × 8` parameter matrix determines the horizontal block of the full
physical tensor, and both selected loadings are specified explicitly.
-/

@[expose] public section

namespace HierarchicalLaminates.Lamination

open Matrix

noncomputable section

def flattenSpatialGradient (F : Matrix (Fin 2) (Fin 16) ℝ) : Gradient (Fin 16) :=
  fun i => F i.1 i.2

def xiFlat : Gradient (Fin 16) := flattenSpatialGradient xiR

def etaFlat : Gradient (Fin 16) := flattenSpatialGradient etaR

/-- The physical tensor has horizontal block `I-PHPᵀ`, common vertical block
`D`, and zero off-diagonal spatial blocks. -/
def materialTensor (H : RMatrix8) : Tensor (Fin 16) :=
  Matrix.of fun i j => if i.1 = j.1 then
    (if i.1 = 0 then horizontalR H else verticalR) i.2 j.2 else 0

theorem materialTensor_eq_spatialBlocks (H : RMatrix8) :
    materialTensor H = spatialBlocks (horizontalR H) verticalR := rfl

theorem materialTensor_energy (H : RMatrix8) (F : Gradient (Fin 16)) :
    quadraticEnergy (materialTensor H) F =
      quadraticFormValue (horizontalR H) (fun a => F (0, a)) +
        quadraticFormValue verticalR (fun a => F (1, a)) := by
  exact spatialBlocks_energy (horizontalR H) verticalR F

theorem normalMatrix_materialTensor (H : RMatrix8) (n : LayerNormal) :
    (normalMatrix n)ᵀ * materialTensor H * normalMatrix n =
      (n.coordinates 0 ^ 2) • horizontalR H + (n.coordinates 1 ^ 2) • verticalR :=
  normalMatrix_spatialBlocks (horizontalR H) verticalR n

theorem materialTensor_average (H₁ H₂ : RMatrix8) (weight : ℝ) :
    matrixAverage weight (materialTensor H₁) (materialTensor H₂) =
      materialTensor (matrixAverage weight H₁ H₂) := by
  have hA : matrixAverage weight (horizontalR H₁) (horizontalR H₂) =
      horizontalR (matrixAverage weight H₁ H₂) := by
    unfold horizontalR matrixAverage
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    module
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases j
  · exact congrFun (congrFun hA a) b
  · simp [materialTensor, matrixAverage]
  · simp [materialTensor, matrixAverage]
  · simp [materialTensor, matrixAverage]
    ring

theorem materialTensor_isHermitian {H : RMatrix8} (hH : H.IsHermitian) :
    (materialTensor H).IsHermitian := by
  have hsandwich := Matrix.isHermitian_mul_mul_conjTranspose factorR hH
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hsandwich
  have hA : (horizontalR H).IsHermitian := Matrix.isHermitian_one.sub hsandwich
  apply Matrix.IsHermitian.ext
  rintro ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases j
  · simpa [materialTensor] using hA.apply a b
  · simp [materialTensor]
  · simp [materialTensor]
  · simpa [materialTensor] using verticalR_posDef.isHermitian.apply a b

theorem materialTensor_posDef {H : RMatrix8} (hH : H.IsHermitian)
    (hA : (horizontalR H).PosDef) : (materialTensor H).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (materialTensor_isHermitian hH)
  intro F hF
  change 0 < quadraticEnergy (materialTensor H) F
  rw [materialTensor_energy]
  have h₀non := hA.posSemidef.dotProduct_mulVec_nonneg (fun a => F (0, a))
  have h₁non := verticalR_posDef.posSemidef.dotProduct_mulVec_nonneg (fun a => F (1, a))
  simp only [star_trivial] at h₀non h₁non
  by_cases hrow : (fun a => F (0, a)) = 0
  · have hrow₁ : (fun a => F (1, a)) ≠ 0 := by
      intro hzero
      apply hF
      ext ⟨i, a⟩
      fin_cases i
      · exact congrFun hrow a
      · exact congrFun hzero a
    have hpos := verticalR_posDef.dotProduct_mulVec_pos hrow₁
    simp only [star_trivial] at hpos
    exact add_pos_of_nonneg_of_pos h₀non hpos
  · have hpos := hA.dotProduct_mulVec_pos hrow
    simp only [star_trivial] at hpos
    exact add_pos_of_pos_of_nonneg hpos h₁non

theorem materialTensor_xi_energy (H : RMatrix8) :
    quadraticEnergy (materialTensor H) xiFlat = 4 / 3 - H 0 0 := by
  have hrow₀ : (fun a => xiFlat (0, a)) = loadPlusR := by
    funext a
    simp [xiFlat, flattenSpatialGradient, xiR, realMatrix, xiQ, loadPlusR, realVector]
  have hrow₁ : (fun a => xiFlat (1, a)) = 0 := by
    funext a
    simp [xiFlat, flattenSpatialGradient, xiR, realMatrix, xiQ]
  rw [materialTensor_energy, hrow₀, hrow₁]
  simpa only [quadraticFormValue, Matrix.mulVec_zero, dotProduct_zero, add_zero]
    using loadPlusR_energy H

theorem materialTensor_eta_energy (H : RMatrix8) :
    quadraticEnergy (materialTensor H) etaFlat = 4 / 3 - H 4 4 := by
  have hrow₀ : (fun a => etaFlat (0, a)) = loadMinusR := by
    funext a
    simp [etaFlat, flattenSpatialGradient, etaR, realMatrix, etaQ, loadMinusR, realVector]
  have hrow₁ : (fun a => etaFlat (1, a)) = 0 := by
    funext a
    simp [etaFlat, flattenSpatialGradient, etaR, realMatrix, etaQ]
  rw [materialTensor_energy, hrow₀, hrow₁]
  simpa only [quadraticFormValue, Matrix.mulVec_zero, dotProduct_zero, add_zero]
    using loadMinusR_energy H

theorem materialTensor_loading_difference (H : RMatrix8) :
    loadingDifference xiFlat etaFlat (materialTensor H) = reducedDifferenceR H := by
  rw [loadingDifference, materialTensor_eta_energy, materialTensor_xi_energy,
    reducedDifferenceR]
  ring

def materialFamily (ρ : ℝ) : Set (Tensor (Fin 16)) :=
  {C | ∃ H : RMatrix8, H ∈ parameterSpace ∧ H.PosSemidef ∧
    (ρ • (1 : RMatrix8) - H).PosSemidef ∧ C = materialTensor H}

def phaseZero : Tensor (Fin 16) := materialTensor 0

def phaseOne (ρ : ℝ) : Tensor (Fin 16) := materialTensor (ρ • (1 : RMatrix8))

theorem phaseZero_mem_materialFamily {ρ : ℝ} (hρ : 0 ≤ ρ) :
    phaseZero ∈ materialFamily ρ := by
  refine ⟨0, parameterSpace.zero_mem, Matrix.PosSemidef.zero, ?_, rfl⟩
  simpa using (Matrix.PosSemidef.one (n := Fin 8) (R := ℝ)).smul hρ

theorem phaseOne_mem_materialFamily {ρ : ℝ} (hρ : 0 ≤ ρ) :
    phaseOne ρ ∈ materialFamily ρ := by
  refine ⟨ρ • (1 : RMatrix8), parameterSpace.smul_mem ρ parameterSpace_one_mem,
    Matrix.PosSemidef.one.smul hρ, ?_, rfl⟩
  simpa using (Matrix.PosSemidef.zero (n := Fin 8) (R := ℝ))

theorem materialFamily_loading_balance {ρ : ℝ} {C : Tensor (Fin 16)}
    (hC : C ∈ materialFamily ρ) : loadingDifference xiFlat etaFlat C = 0 := by
  rcases hC with ⟨H, hH, _, _, rfl⟩
  rw [materialTensor_loading_difference]
  exact reducedDifferenceR_zero_of_spinMember hH

theorem materialFamily_posDef {ρ : ℝ} (hρ : 0 ≤ ρ) (hρlt : ρ < 2 / 3)
    {C : Tensor (Fin 16)} (hC : C ∈ materialFamily ρ) : C.PosDef := by
  rcases hC with ⟨H, _, hlower, hupper, rfl⟩
  exact materialTensor_posDef hlower.isHermitian (horizontalR_posDef hupper hρ hρlt)

end

end HierarchicalLaminates.Lamination
