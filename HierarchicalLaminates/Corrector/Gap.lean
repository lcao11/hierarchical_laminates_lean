module

public import HierarchicalLaminates.Corrector.CellIdentification
public import HierarchicalLaminates.Fourier.ContinuousGap

/-!
# The reduced loading gap equals the smooth cell-energy gap
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Corrector

open Matrix HierarchicalLaminates.Fourier HierarchicalLaminates.Periodic HierarchicalLaminates.Lamination
  HierarchicalLaminates.Material

lemma effective_horizontal_energy (z : PotentialVector) :
    quadraticEnergy (effectiveMatrix smoothFraction)
      (horizontalLoading z : PhysicalIndex → ℝ) =
    quadraticEnergy (materialTensor meanResponseMatrix)
      (horizontalLoading z : PhysicalIndex → ℝ) := by
  have h := effective_horizontal_operator z
  rw [← effectiveMatrix_operator] at h
  exact congrArg (fun v : PhysicalGradient =>
    (horizontalLoading z : PhysicalIndex → ℝ) ⬝ᵥ (v : PhysicalIndex → ℝ)) h

lemma horizontalLoading_plus :
    horizontalLoading (WithLp.toLp 2 loadPlusR) = WithLp.toLp 2 xiFlat := by
  ext ⟨i, a⟩
  fin_cases i <;>
    simp [horizontalLoading, xiFlat, flattenSpatialGradient,
      xiR_horizontal_row, xiR_vertical_row]

lemma horizontalLoading_minus :
    horizontalLoading (WithLp.toLp 2 loadMinusR) = WithLp.toLp 2 etaFlat := by
  ext ⟨i, a⟩
  fin_cases i <;>
    simp [horizontalLoading, etaFlat, flattenSpatialGradient,
      etaR_horizontal_row, etaR_vertical_row]

lemma smooth_physical_loading_gap :
    physicalLoadingDifference smoothFraction = reducedDifferenceR meanResponseMatrix := by
  have hp := effective_horizontal_energy (WithLp.toLp 2 loadPlusR)
  have hm := effective_horizontal_energy (WithLp.toLp 2 loadMinusR)
  rw [horizontalLoading_plus] at hp
  rw [horizontalLoading_minus] at hm
  change quadraticEnergy (effectiveMatrix smoothFraction) xiFlat =
    quadraticEnergy (materialTensor meanResponseMatrix) xiFlat at hp
  change quadraticEnergy (effectiveMatrix smoothFraction) etaFlat =
    quadraticEnergy (materialTensor meanResponseMatrix) etaFlat at hm
  change quadraticEnergy (effectiveMatrix smoothFraction) etaFlat -
      quadraticEnergy (effectiveMatrix smoothFraction) xiFlat = _
  rw [hp, hm]
  exact materialTensor_loading_difference _

lemma meanResponseMatrix_difference :
    reducedDifferenceR meanResponseMatrix = HierarchicalLaminates.operatorDifference (rhoSolution (0, 0)) := by
  rw [← HierarchicalLaminates.operatorDifference_matrix meanResponseMatrix]
  congr 1
  exact (Matrix.toEuclideanCLM (𝕜 := ℝ)).apply_symm_apply _


/-- The reduced loading difference equals the smooth coefficient law's cell-energy difference. -/
lemma smooth_physical_loading_gap_eq_sequence :
    physicalLoadingDifference smoothFraction = HierarchicalLaminates.sequenceLoading rhoSolution := by
  rw [smooth_physical_loading_gap, meanResponseMatrix_difference]
  exact (HierarchicalLaminates.sequenceLoading_apply rhoSolution).symm

lemma smooth_physical_loading_gap_positive :
    0 < physicalLoadingDifference smoothFraction := by
  rw [smooth_physical_loading_gap_eq_sequence]
  exact HierarchicalLaminates.reduced_solution_gap_positive

end HierarchicalLaminates.Corrector
