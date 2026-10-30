module

public import HierarchicalLaminates.Corrector.BinaryComparison
public import HierarchicalLaminates.Binary.SampledProfileEstimate

/-! The concrete equilibrated trial flux for every positive stripe count. -/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Corrector

open HierarchicalLaminates.Periodic HierarchicalLaminates.Material HierarchicalLaminates.Binary

def binaryTrialFlux (N : ℕ) (hN : 0 < N) (z : PotentialVector) : PhysicalField :=
  correctedFlux (binaryPrimitiveField N hN) (binaryPrimitiveDerivativeFields N hN) z

lemma binaryTrialFlux_orthogonal (N : ℕ) (hN : 0 < N) (z : PotentialVector)
    (g : PhysicalField) (hg : g ∈ gradientSpace) :
    inner ℝ (binaryTrialFlux N hN z) g = 0 :=
  correctedFlux_orthogonal _ _ (fun i test => binaryPrimitive_weakPairing hN i test) z g hg

lemma binaryTrialFlux_mean (N : ℕ) (hN : 0 < N) (z : PotentialVector) :
    meanField (binaryTrialFlux N hN z) =
      HierarchicalLaminates.Material.effectiveOperator smoothFraction (horizontalLoading z) :=
  correctedFlux_mean _ _ (fun i test => binaryPrimitive_weakPairing hN i test) z

def binaryResidual (N : ℕ) (hN : 0 < N) (z : PotentialVector) : PhysicalField :=
  comparisonResidual (binaryFraction N) z (binaryTrialFlux N hN z)

lemma binaryResponse_error (N : ℕ) (hN : 0 < N) (z : PotentialVector) :
    ‖HierarchicalLaminates.Material.effectiveOperator (binaryFraction N) (horizontalLoading z) -
      HierarchicalLaminates.Material.effectiveOperator smoothFraction (horizontalLoading z)‖ ≤
      5 * ‖binaryResidual N hN z‖ :=
  actual_response_error_bound _ z _ (binaryTrialFlux_orthogonal N hN z) (binaryTrialFlux_mean N hN z)

lemma binaryLoadingEnergy_error (N : ℕ) (hN : 0 < N) (z : PotentialVector) :
    |inner ℝ (HierarchicalLaminates.Material.effectiveOperator (binaryFraction N) (horizontalLoading z)) (horizontalLoading z) -
      inner ℝ (HierarchicalLaminates.Material.effectiveOperator smoothFraction (horizontalLoading z)) (horizontalLoading z)| ≤
      5 * ‖horizontalLoading z‖ * ‖binaryResidual N hN z‖ :=
  actual_loading_energy_error_bound _ z _ (binaryTrialFlux_orthogonal N hN z) (binaryTrialFlux_mean N hN z)

end HierarchicalLaminates.Corrector
