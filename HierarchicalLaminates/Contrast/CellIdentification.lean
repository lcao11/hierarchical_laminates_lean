module

public import HierarchicalLaminates.Contrast.Law
public import HierarchicalLaminates.Contrast.Response
public import HierarchicalLaminates.Corrector.Gap

/-!
# Identification of the response with the periodic cell problem

For `0 ≤ r < 2 / 3`, the field synthesized from the Neumann response is a
gradient perturbation of each constant horizontal loading. Its flux is
orthogonal to all periodic weak gradients, so uniqueness identifies it with
the cell solver for `coefficientLaw r smoothFraction`.

Taking the mean flux gives the horizontal effective response. In particular,
`physicalGap_eq_sequence` identifies the selected weak-H¹ cell-energy
difference with the coefficient-space loading functional.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.Contrast

open Matrix MeasureTheory Fourier Periodic Lamination Material Analysis Corrector

def totalContinuous (r : ℝ) (z : PotentialVector) : C(PeriodicDomain, PhysicalGradient) :=
  ContinuousMap.const PeriodicDomain (horizontalLoading z) +
    gradientContinuous (solution r) (reducedLoading z)

lemma response_constitutive_identity {r : ℝ} (hr : 0 ≤ r) (hrlt : r < 2/3)
    (w : ReducedSpace) (q : PeriodicDomain) :
    (r*cosineProfile q) •
      (w+WithLp.toLp 2 (factorRᵀ *ᵥ (fun a => gradientContinuous (solution r) w q (0,a)))) =
      response r q w := by
  rw [reduced_gradient_synthesis]
  have h := congrArg (fun M : C(PeriodicDomain,ReducedOperator) => M q w)
    (response_equation hr hrlt)
  simpa only [ContinuousMap.smul_apply,ContinuousMap.smul_apply',ContinuousMap.add_apply,
    ContinuousMap.const_apply,_root_.smul_apply,_root_.add_apply,
    ContinuousLinearMap.id_apply,← smul_smul] using h.symm

lemma horizontal_source_identity {r : ℝ} (hr : 0 ≤ r) (hrlt : r < 2/3) (z : PotentialVector) (q : PeriodicDomain) :
    (r * cosineProfile q) •
      (factorRᵀ *ᵥ (fun a => totalContinuous r z q (0, a))) =
        (response r q (reducedLoading z) : Fin 8 → ℝ) := by
  have h := congrArg (fun v : ReducedSpace => (v : Fin 8 → ℝ))
    (response_constitutive_identity hr hrlt (reducedLoading z) q)
  change (r * cosineProfile q) •
    ((factorRᵀ *ᵥ (z : Fin 16 → ℝ)) +
      factorRᵀ *ᵥ (fun a => gradientContinuous (solution r) (reducedLoading z) q (0, a))) = _ at h
  rw [← Matrix.mulVec_add] at h
  exact h

lemma total_flux_pointwise {r : ℝ} (hr : 0 ≤ r) (hrlt : r < 2/3) (z : PotentialVector) (q : PeriodicDomain) :
    coefficientOperator r smoothFraction q (totalContinuous r z q) =
      horizontalLoading z + fluxContinuous (solution r) (reducedLoading z) q := by
  rw [coefficientOperator_eq_matrix]
  change Matrix.toEuclideanCLM (𝕜 := ℝ)
    (materialTensor ((r * cosineProfile q) • (1 : HierarchicalLaminates.RMatrix8)))
    (totalContinuous r z q) = _
  ext ⟨i, a⟩
  change (materialTensor _ *ᵥ (totalContinuous r z q : PhysicalIndex → ℝ)) (i, a) = _
  rw [materialTensor_mulVec_rows]
  change _ = horizontalLoading z (i, a) + fluxContinuous (solution r) (reducedLoading z) q (i, a)
  rw [fluxContinuous_component]
  fin_cases i
  · norm_num only [Fin.ext_iff] at *
    have hsource := congrArg (fun v : Fin 8 → ℝ => (factorR *ᵥ v) a)
      (horizontal_source_identity hr hrlt z q)
    have hsource' : (r * cosineProfile q) *
        (factorR *ᵥ (factorRᵀ *ᵥ (fun b => totalContinuous r z q (0, b)))) a =
      amplitudeOperator (reducedLoading z) a (response r q) := by
      simpa only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
        amplitudeOperator_apply] using hsource
    simp only [horizontalR, Matrix.sub_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hsource']
    simp [totalContinuous, horizontalLoading, response, sub_eq_add_neg, add_assoc]
  · norm_num only [Fin.ext_iff]
    rw [verticalR_diagonal, Matrix.mulVec_diagonal]
    simp [totalContinuous, horizontalLoading]

lemma total_flux_L2 {r : ℝ} (hr : 0 ≤ r) (hrlt : r < 2/3) (z : PotentialVector) :
    coefficientLaw r smoothFraction (continuousField (totalContinuous r z)) =
      constantField (horizontalLoading z) +
        continuousField (fluxContinuous (solution r) (reducedLoading z)) := by
  apply Lp.ext
  filter_upwards [coefficientLaw_coe r smoothFraction (continuousField (totalContinuous r z)),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure (totalContinuous r z),
    Lp.coeFn_add (constantField (horizontalLoading z))
      (continuousField (fluxContinuous (solution r) (reducedLoading z))),
    Lp.coeFn_const 2 domainMeasure (horizontalLoading z),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure
      (fluxContinuous (solution r) (reducedLoading z))] with q hL htotal hadd hconst hflux
  change continuousField (totalContinuous r z) q = totalContinuous r z q at htotal
  change constantField (horizontalLoading z) q = horizontalLoading z at hconst
  change continuousField (fluxContinuous (solution r) (reducedLoading z)) q = _ at hflux
  rw [hL, htotal, hadd]
  simp only [Pi.add_apply]
  rw [hconst, hflux]
  exact total_flux_pointwise hr hrlt z q

lemma total_isCellField {r : ℝ} (hr : 0 ≤ r) (hrlt : r < 2/3) (z : PotentialVector) :
    IsCellField gradientSpace (coefficientLaw r smoothFraction) (constantField (horizontalLoading z))
      (continuousField (totalContinuous r z)) := by
  constructor
  · simp only [totalContinuous, map_add, continuousField_const, add_sub_cancel_left]
    exact physical_gradient_admissible (solution r) (reducedLoading z)
  · intro g hg
    rw [total_flux_L2 hr hrlt, inner_add_left]
    have hc : inner ℝ (constantField (horizontalLoading z)) g = 0 := by
      rw [constant_mean_pairing, gradientSpace_mean_zero g hg, inner_zero_right]
    rw [hc, zero_add]
    exact cosineSynthesis_gradient_zero _ (fluxCoefficients_divergence (solution r) (reducedLoading z)) g hg

lemma total_eq_cellField {r : ℝ} (hr : 0 ≤ r) (hrlt : r < 2/3) (z : PotentialVector) :
    continuousField (totalContinuous r z) =
      cellField gradientSpace (coefficientLaw r smoothFraction) (ellipticity r)
        (ellipticity_pos hrlt) (coefficientLaw_coercive hr smoothFraction)
        (constantField (horizontalLoading z)) := by
  apply cellField_unique (ellipticity_pos hrlt)
    (coefficientLaw_coercive hr smoothFraction) (total_isCellField hr hrlt z)
  exact cellField_isCellField _ _ _ _ _ _

lemma effective_horizontal_mean {r : ℝ} (hr : 0 ≤ r) (hrlt : r < 2/3) (z : PotentialVector) :
    effectiveOperator r hr hrlt smoothFraction (horizontalLoading z) =
      horizontalLoading z + fluxCoefficients (solution r) (reducedLoading z) (0, 0) := by
  change meanField (coefficientLaw r smoothFraction
    (cellField gradientSpace (coefficientLaw r smoothFraction) (ellipticity r)
      (ellipticity_pos hrlt) (coefficientLaw_coercive hr smoothFraction)
      (constantField (horizontalLoading z)))) = _
  rw [← total_eq_cellField hr hrlt, total_flux_L2 hr hrlt, map_add, mean_constantField]
  congr 1
  change meanContinuous (fluxContinuous (solution r) (reducedLoading z)) = _
  rw [meanContinuous_eq_integral, ← uniformMean_eq_integral]
  exact cosineSynthesis_mean _

def meanResponseMatrix (r : ℝ) : HierarchicalLaminates.RMatrix8 :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ)).symm ((solution r) (0, 0))

lemma meanResponseMatrix_action (r : ℝ) (w : ReducedSpace) :
    meanResponseMatrix r *ᵥ (w : Fin 8 → ℝ) = ((solution r) (0, 0) w : Fin 8 → ℝ) := by
  have h := congrArg (fun L : ReducedOperator => (L w : Fin 8 → ℝ))
    ((Matrix.toEuclideanCLM (𝕜 := ℝ)).apply_symm_apply ((solution r) (0, 0)))
  exact h

lemma effective_horizontal_operator {r : ℝ} (hr : 0 ≤ r) (hrlt : r < 2/3) (z : PotentialVector) :
    effectiveOperator r hr hrlt smoothFraction (horizontalLoading z) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (materialTensor (meanResponseMatrix r))
        (horizontalLoading z) := by
  rw [effective_horizontal_mean hr hrlt]
  ext ⟨i, a⟩
  change (horizontalLoading z + fluxCoefficients (solution r) (reducedLoading z) (0, 0)) (i, a) =
    (materialTensor (meanResponseMatrix r) *ᵥ (horizontalLoading z : PhysicalIndex → ℝ)) (i, a)
  rw [materialTensor_mulVec_rows]
  simp only [fluxCoefficients]
  fin_cases i
  · simp [horizontalLoading, fluxComponentCoefficients, gradientCoefficients,
      gradientMultiplier, frequencyVector, horizontalR, Matrix.sub_mulVec,
      Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      amplitudeCoefficients_apply, amplitudeOperator_apply,
      reducedLoading]
    simpa only [reducedLoading, sub_eq_add_neg] using
      congrArg (fun v : Fin 8 → ℝ => z a - (factorR *ᵥ v) a)
        (meanResponseMatrix_action r (reducedLoading z)).symm
  · simp [horizontalLoading, fluxComponentCoefficients, gradientCoefficients,
      gradientMultiplier, frequencyVector]
    exact (congrFun (Matrix.mulVec_zero verticalR) a).symm

theorem effective_horizontal_energy {r : ℝ} (hr : 0 ≤ r) (hrlt : r < 2/3)
    (z : PotentialVector) :
    quadraticEnergy (effectiveMatrix r hr hrlt smoothFraction)
      (horizontalLoading z : PhysicalIndex → ℝ) =
    quadraticEnergy (materialTensor (meanResponseMatrix r))
      (horizontalLoading z : PhysicalIndex → ℝ) := by
  have h := effective_horizontal_operator hr hrlt z
  rw [← effectiveMatrix_operator r hr hrlt smoothFraction] at h
  exact congrArg (fun v : PhysicalGradient =>
    (horizontalLoading z : PhysicalIndex → ℝ) ⬝ᵥ (v : PhysicalIndex → ℝ)) h

/-- For `0 ≤ r < 2 / 3`, the Neumann loading response equals the selected
weak-H¹ cell-energy difference for `smoothFraction`. -/
theorem physicalGap_eq_sequence {r : ℝ} (hr : 0 ≤ r) (hrlt : r < 2/3) :
    physicalGap r = sequenceLoading (solution r) := by
  have hp := effective_horizontal_energy hr hrlt (WithLp.toLp 2 loadPlusR)
  have hm := effective_horizontal_energy hr hrlt (WithLp.toLp 2 loadMinusR)
  rw [horizontalLoading_plus] at hp
  rw [horizontalLoading_minus] at hm
  change quadraticEnergy (effectiveMatrix r hr hrlt smoothFraction) xiFlat = _ at hp
  change quadraticEnergy (effectiveMatrix r hr hrlt smoothFraction) etaFlat = _ at hm
  rw [physicalGap,← effectiveMatrix_quadratic_energy r hr hrlt smoothFraction,
    ← effectiveMatrix_quadratic_energy r hr hrlt smoothFraction,hm,hp]
  change loadingDifference xiFlat etaFlat (materialTensor (meanResponseMatrix r)) = _
  rw [materialTensor_loading_difference,sequenceLoading_apply]
  rw [← operatorDifference_matrix (meanResponseMatrix r)]
  congr 1
  exact (Matrix.toEuclideanCLM (𝕜 := ℝ)).apply_symm_apply _


end HierarchicalLaminates.Contrast
