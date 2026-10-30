module

public import HierarchicalLaminates.Corrector.CellIdentification
public import HierarchicalLaminates.Analysis.Residual
public import HierarchicalLaminates.Corrector.ProductPotential

/-!
# Effective-response comparison from a constitutive residual

The smooth Sobolev cell field is used as a trial field for any phase-fraction
coefficient law, including the binary stripe arrangements.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Corrector

open HierarchicalLaminates.Fourier HierarchicalLaminates.Periodic HierarchicalLaminates.Analysis HierarchicalLaminates.Material

def comparisonResidual (b : PhaseFraction) (z : PotentialVector) (j : PhysicalField) : PhysicalField :=
  j - coefficientLaw b (continuousField (totalContinuous z))

lemma actual_response_error_bound (b : PhaseFraction) (z : PotentialVector)
    (j : PhysicalField)
    (hjorth : ∀ g ∈ gradientSpace, inner ℝ j g = 0)
    (hjmean : meanField j = HierarchicalLaminates.Material.effectiveOperator smoothFraction (horizontalLoading z)) :
    ‖HierarchicalLaminates.Material.effectiveOperator b (horizontalLoading z) -
      HierarchicalLaminates.Material.effectiveOperator smoothFraction (horizontalLoading z)‖ ≤
      5 * ‖comparisonResidual b z j‖ := by
  let eB := cellField gradientSpace (coefficientLaw b) (1 / 4)
    (by norm_num) (coefficientLaw_coercive b) (constantField (horizontalLoading z))
  let eS := continuousField (totalContinuous z)
  let de := eB - eS
  let dj := coefficientLaw b eB - j
  have heB : IsCellField gradientSpace (coefficientLaw b) (constantField (horizontalLoading z)) eB :=
    cellField_isCellField _ _ _ _ _ _
  have hde : de ∈ gradientSpace := by
    have hs := (total_isCellField z).1
    simpa only [sub_sub_sub_cancel_right] using gradientSpace.sub_mem heB.1 hs
  have horth : inner ℝ dj de = 0 := by
    dsimp [dj]
    rw [inner_sub_left, heB.2 de hde, hjorth de hde, sub_self]
  have hr : comparisonResidual b z j = coefficientLaw b de - dj := by
    dsimp [comparisonResidual, de, dj, eS]
    rw [map_sub]
    abel
  have hbound := response_error_bound meanField meanField_norm_le
    (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (0 : ℝ) ≤ 1)
    (coefficientLaw_coercive b)
    (fun v => by simpa only [one_mul] using coefficientLaw_norm_le b v)
    de dj (comparisonResidual b z j) hr horth
  have hmean : meanField dj =
      HierarchicalLaminates.Material.effectiveOperator b (horizontalLoading z) -
        HierarchicalLaminates.Material.effectiveOperator smoothFraction (horizontalLoading z) := by
    dsimp [dj]
    rw [map_sub, hjmean]
    rfl
  rw [hmean] at hbound
  norm_num at hbound ⊢
  exact hbound

lemma actual_loading_energy_error_bound (b : PhaseFraction) (z : PotentialVector)
    (j : PhysicalField)
    (hjorth : ∀ g ∈ gradientSpace, inner ℝ j g = 0)
    (hjmean : meanField j = HierarchicalLaminates.Material.effectiveOperator smoothFraction (horizontalLoading z)) :
    |inner ℝ (HierarchicalLaminates.Material.effectiveOperator b (horizontalLoading z)) (horizontalLoading z) -
      inner ℝ (HierarchicalLaminates.Material.effectiveOperator smoothFraction (horizontalLoading z))
        (horizontalLoading z)| ≤
      5 * ‖horizontalLoading z‖ * ‖comparisonResidual b z j‖ := by
  rw [← inner_sub_left]
  calc
    |inner ℝ
        (HierarchicalLaminates.Material.effectiveOperator b (horizontalLoading z) -
          HierarchicalLaminates.Material.effectiveOperator smoothFraction (horizontalLoading z))
        (horizontalLoading z)| ≤
      ‖HierarchicalLaminates.Material.effectiveOperator b (horizontalLoading z) -
          HierarchicalLaminates.Material.effectiveOperator smoothFraction (horizontalLoading z)‖ *
        ‖horizontalLoading z‖ := abs_real_inner_le_norm _ _
    _ ≤ (5 * ‖comparisonResidual b z j‖) * ‖horizontalLoading z‖ :=
      mul_le_mul_of_nonneg_right (actual_response_error_bound b z j hjorth hjmean) (norm_nonneg _)
    _ = _ := by ring

lemma smooth_flux_mean (z : PotentialVector) :
    meanField (coefficientLaw smoothFraction (continuousField (totalContinuous z))) =
      HierarchicalLaminates.Material.effectiveOperator smoothFraction (horizontalLoading z) := by
  change _ = meanField (coefficientLaw smoothFraction
    (cellField gradientSpace (coefficientLaw smoothFraction) (1 / 4)
      (by norm_num) (coefficientLaw_coercive smoothFraction) (constantField (horizontalLoading z))))
  rw [← total_eq_cellField]

def correctedFlux (p : ScalarField) (dp : Fin 2 → ScalarField) (z : PotentialVector) : PhysicalField :=
  coefficientLaw smoothFraction (continuousField (totalContinuous z)) +
    HierarchicalLaminates.rho • HierarchicalLaminates.WeakCalculus.curlField (productGradient p dp z)

lemma correctedFlux_orthogonal (p : ScalarField) (dp : Fin 2 → ScalarField)
    (hp : ∀ i, ScalarWeakPartial p (dp i) i) (z : PotentialVector)
    (g : PhysicalField) (hg : g ∈ gradientSpace) :
    inner ℝ (correctedFlux p dp z) g = 0 := by
  rw [correctedFlux, inner_add_left, real_inner_smul_left,
    (total_isCellField z).2 g hg, product_curl_orthogonal p dp hp z g hg]
  ring

lemma correctedFlux_mean (p : ScalarField) (dp : Fin 2 → ScalarField)
    (hp : ∀ i, ScalarWeakPartial p (dp i) i) (z : PotentialVector) :
    meanField (correctedFlux p dp z) =
      HierarchicalLaminates.Material.effectiveOperator smoothFraction (horizontalLoading z) := by
  rw [correctedFlux, map_add, map_smul, product_curl_mean_zero p dp hp z,
    smul_zero, add_zero, smooth_flux_mean]

lemma correctedFlux_response_error (b : PhaseFraction) (p : ScalarField)
    (dp : Fin 2 → ScalarField) (hp : ∀ i, ScalarWeakPartial p (dp i) i) (z : PotentialVector) :
    ‖HierarchicalLaminates.Material.effectiveOperator b (horizontalLoading z) -
      HierarchicalLaminates.Material.effectiveOperator smoothFraction (horizontalLoading z)‖ ≤
      5 * ‖comparisonResidual b z (correctedFlux p dp z)‖ :=
  actual_response_error_bound b z _ (correctedFlux_orthogonal p dp hp z) (correctedFlux_mean p dp hp z)

end HierarchicalLaminates.Corrector
