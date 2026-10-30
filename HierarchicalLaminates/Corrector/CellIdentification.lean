module

public import HierarchicalLaminates.Corrector.Synthesis
public import HierarchicalLaminates.Fourier.FluxOrthogonality
public import HierarchicalLaminates.Material.Arrangements

/-!
# Identification with the periodic cell solution
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Corrector

open Matrix MeasureTheory HierarchicalLaminates.Fourier HierarchicalLaminates.Periodic
  HierarchicalLaminates.Lamination HierarchicalLaminates.Material HierarchicalLaminates.Analysis

def horizontalLoading (z : PotentialVector) : PhysicalGradient :=
  WithLp.toLp 2 (fun j => if j.1 = 0 then z j.2 else 0)

def reducedLoading (z : PotentialVector) : ReducedSpace :=
  WithLp.toLp 2 (factorRᵀ *ᵥ (z : Fin 16 → ℝ))

def totalContinuous (z : PotentialVector) : C(PeriodicDomain, PhysicalGradient) :=
  ContinuousMap.const PeriodicDomain (horizontalLoading z) +
    gradientContinuous rhoSolution (reducedLoading z)

lemma materialTensor_mulVec_rows (H : HierarchicalLaminates.RMatrix8)
    (F : PhysicalGradient) (i : Fin 2) (a : Fin 16) :
    (materialTensor H *ᵥ (F : PhysicalIndex → ℝ)) (i, a) =
      if i = 0 then (horizontalR H *ᵥ (fun b => F (0, b))) a
      else (verticalR *ᵥ (fun b => F (1, b))) a := by
  fin_cases i <;>
    simp [materialTensor, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_succ]

lemma horizontal_source_identity (z : PotentialVector) (q : PeriodicDomain) :
    (HierarchicalLaminates.rho * cosineProfile q) •
      (factorRᵀ *ᵥ (fun a => totalContinuous z q (0, a))) =
        (reducedResponse q (reducedLoading z) : Fin 8 → ℝ) := by
  have h := congrArg (fun v : ReducedSpace => (v : Fin 8 → ℝ))
    (response_constitutive_identity (reducedLoading z) q)
  change (HierarchicalLaminates.rho * cosineProfile q) •
    ((factorRᵀ *ᵥ (z : Fin 16 → ℝ)) +
      factorRᵀ *ᵥ (fun a => gradientContinuous rhoSolution (reducedLoading z) q (0, a))) = _ at h
  rw [← Matrix.mulVec_add] at h
  exact h

lemma mixtureTensor_material (t : ℝ) :
    mixtureTensor t = materialTensor ((HierarchicalLaminates.rho * t) • (1 : HierarchicalLaminates.RMatrix8)) := by
  unfold mixtureTensor phaseZero phaseOne
  rw [add_comm]
  change matrixAverage t (materialTensor (HierarchicalLaminates.rho • 1)) (materialTensor 0) = _
  rw [materialTensor_average]
  simp [matrixAverage, smul_smul, mul_comm]

lemma total_flux_pointwise (z : PotentialVector) (q : PeriodicDomain) :
    coefficientOperator smoothFraction q (totalContinuous z q) =
      horizontalLoading z + fluxContinuous rhoSolution (reducedLoading z) q := by
  rw [coefficientOperator_eq_matrix, mixtureTensor_material]
  change Matrix.toEuclideanCLM (𝕜 := ℝ)
    (materialTensor ((HierarchicalLaminates.rho * cosineProfile q) • (1 : HierarchicalLaminates.RMatrix8)))
    (totalContinuous z q) = _
  ext ⟨i, a⟩
  change (materialTensor _ *ᵥ (totalContinuous z q : PhysicalIndex → ℝ)) (i, a) = _
  rw [materialTensor_mulVec_rows]
  change _ = horizontalLoading z (i, a) + fluxContinuous rhoSolution (reducedLoading z) q (i, a)
  rw [fluxContinuous_component]
  fin_cases i
  · norm_num only [Fin.ext_iff] at *
    have hsource := congrArg (fun v : Fin 8 → ℝ => (factorR *ᵥ v) a)
      (horizontal_source_identity z q)
    have hsource' : (HierarchicalLaminates.rho * cosineProfile q) *
        (factorR *ᵥ (factorRᵀ *ᵥ (fun b => totalContinuous z q (0, b)))) a =
      amplitudeOperator (reducedLoading z) a (reducedResponse q) := by
      simpa only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
        amplitudeOperator_apply] using hsource
    simp only [horizontalR, Matrix.sub_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hsource']
    simp [totalContinuous, horizontalLoading, reducedResponse, sub_eq_add_neg, add_assoc]
  · norm_num only [Fin.ext_iff]
    rw [verticalR_diagonal, Matrix.mulVec_diagonal]
    simp [totalContinuous, horizontalLoading]

lemma total_flux_L2 (z : PotentialVector) :
    coefficientLaw smoothFraction (continuousField (totalContinuous z)) =
      constantField (horizontalLoading z) +
        continuousField (fluxContinuous rhoSolution (reducedLoading z)) := by
  apply Lp.ext
  filter_upwards [coefficientLaw_coe smoothFraction (continuousField (totalContinuous z)),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure (totalContinuous z),
    Lp.coeFn_add (constantField (horizontalLoading z))
      (continuousField (fluxContinuous rhoSolution (reducedLoading z))),
    Lp.coeFn_const 2 domainMeasure (horizontalLoading z),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure
      (fluxContinuous rhoSolution (reducedLoading z))] with q hL htotal hadd hconst hflux
  change continuousField (totalContinuous z) q = totalContinuous z q at htotal
  change constantField (horizontalLoading z) q = horizontalLoading z at hconst
  change continuousField (fluxContinuous rhoSolution (reducedLoading z)) q = _ at hflux
  rw [hL, htotal, hadd]
  simp only [Pi.add_apply]
  rw [hconst, hflux]
  exact total_flux_pointwise z q

lemma total_isCellField (z : PotentialVector) :
    IsCellField gradientSpace (coefficientLaw smoothFraction) (constantField (horizontalLoading z))
      (continuousField (totalContinuous z)) := by
  constructor
  · simp only [totalContinuous, map_add, continuousField_const, add_sub_cancel_left]
    exact physical_gradient_admissible rhoSolution (reducedLoading z)
  · intro g hg
    rw [total_flux_L2, inner_add_left]
    have hc : inner ℝ (constantField (horizontalLoading z)) g = 0 := by
      rw [constant_mean_pairing, gradientSpace_mean_zero g hg, inner_zero_right]
    rw [hc, zero_add]
    exact cosineSynthesis_gradient_zero _ (fluxCoefficients_divergence rhoSolution (reducedLoading z)) g hg

lemma total_eq_cellField (z : PotentialVector) :
    continuousField (totalContinuous z) =
      cellField gradientSpace (coefficientLaw smoothFraction) (1 / 4)
        (by norm_num) (coefficientLaw_coercive smoothFraction)
        (constantField (horizontalLoading z)) := by
  apply cellField_unique (by norm_num : (0 : ℝ) < 1 / 4)
    (coefficientLaw_coercive smoothFraction) (total_isCellField z)
  exact cellField_isCellField _ _ _ _ _ _

lemma effective_horizontal_mean (z : PotentialVector) :
    HierarchicalLaminates.Material.effectiveOperator smoothFraction (horizontalLoading z) =
      horizontalLoading z + fluxCoefficients rhoSolution (reducedLoading z) (0, 0) := by
  change meanField (coefficientLaw smoothFraction
    (cellField gradientSpace (coefficientLaw smoothFraction) (1 / 4)
      (by norm_num) (coefficientLaw_coercive smoothFraction)
      (constantField (horizontalLoading z)))) = _
  rw [← total_eq_cellField, total_flux_L2, map_add, mean_constantField]
  congr 1
  change meanContinuous (fluxContinuous rhoSolution (reducedLoading z)) = _
  rw [meanContinuous_eq_integral, ← uniformMean_eq_integral]
  exact cosineSynthesis_mean _

def meanResponseMatrix : HierarchicalLaminates.RMatrix8 :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ)).symm (rhoSolution (0, 0))

lemma meanResponseMatrix_action (w : ReducedSpace) :
    meanResponseMatrix *ᵥ (w : Fin 8 → ℝ) = (rhoSolution (0, 0) w : Fin 8 → ℝ) := by
  have h := congrArg (fun L : ReducedOperator => (L w : Fin 8 → ℝ))
    ((Matrix.toEuclideanCLM (𝕜 := ℝ)).apply_symm_apply (rhoSolution (0, 0)))
  exact h

lemma effective_horizontal_operator (z : PotentialVector) :
    HierarchicalLaminates.Material.effectiveOperator smoothFraction (horizontalLoading z) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (materialTensor meanResponseMatrix)
        (horizontalLoading z) := by
  rw [effective_horizontal_mean]
  ext ⟨i, a⟩
  change (horizontalLoading z + fluxCoefficients rhoSolution (reducedLoading z) (0, 0)) (i, a) =
    (materialTensor meanResponseMatrix *ᵥ (horizontalLoading z : PhysicalIndex → ℝ)) (i, a)
  rw [materialTensor_mulVec_rows]
  simp only [fluxCoefficients, assembleCoefficients_apply]
  fin_cases i
  · simp [horizontalLoading, fluxComponentCoefficients, gradientCoefficients,
      gradientMultiplier, frequencyVector, horizontalR, Matrix.sub_mulVec,
      Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      amplitudeCoefficients_apply, amplitudeOperator_apply, meanResponseMatrix_action,
      reducedLoading]
    simpa only [reducedLoading, sub_eq_add_neg] using
      congrArg (fun v : Fin 8 → ℝ => z a - (factorR *ᵥ v) a)
        (meanResponseMatrix_action (reducedLoading z)).symm
  · simp [horizontalLoading, fluxComponentCoefficients, gradientCoefficients,
      gradientMultiplier, frequencyVector]
    exact (congrFun (Matrix.mulVec_zero verticalR) a).symm

end HierarchicalLaminates.Corrector
