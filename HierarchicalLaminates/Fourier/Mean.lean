module

public import HierarchicalLaminates.Fourier.CosineProfile
public import HierarchicalLaminates.Periodic.FieldSpace
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Means of the real synthesized fields

The measure is the explicit normalized product Haar measure from the periodic
field interface. The coefficient values need only form a real Banach space;
in particular, this applies to Euclidean operators with their operator norm.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Fourier

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def uniformMean : C(PeriodicDomain, E) →L[ℝ] E :=
  (L1.integralCLM (α := PeriodicDomain) (E := E) (μ := HierarchicalLaminates.Periodic.domainMeasure)).comp
    (ContinuousMap.toLp 1 HierarchicalLaminates.Periodic.domainMeasure ℝ)

theorem uniformMean_eq_integral (f : C(PeriodicDomain, E)) :
    uniformMean f = ∫ x, f x ∂HierarchicalLaminates.Periodic.domainMeasure := by
  change L1.integralCLM (ContinuousMap.toLp 1 HierarchicalLaminates.Periodic.domainMeasure ℝ f) = _
  rw [← L1.integral_eq, L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ)
    HierarchicalLaminates.Periodic.domainMeasure f)

theorem uniformMean_constant (c : E) :
    uniformMean (ContinuousMap.const PeriodicDomain c) = c := by
  rw [uniformMean_eq_integral]
  simp

section CharacterIntegrals

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem integral_unitFourier (n : ℤ) :
    (∫ x : AddCircle (1 : ℝ), fourier n x ∂AddCircle.haarAddCircle) =
      if n = 0 then (1 : ℂ) else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) n) 0
  simpa [fourierCoeff, Pi.single_apply, eq_comm] using h

theorem integral_phaseCharacter (k : ℤ × ℤ) :
    (∫ x, phaseCharacter k x ∂HierarchicalLaminates.Periodic.domainMeasure) =
      if k = (0, 0) then (1 : ℂ) else 0 := by
  change (∫ x : UnitAddTorus (Fin 2),
    ∏ i : Fin 2, fourier (frequencyVector k i) (x i)) = _
  rw [MeasureTheory.integral_fintype_prod_volume_eq_prod]
  change (∏ i : Fin 2, ∫ x : AddCircle (1 : ℝ),
    fourier (frequencyVector k i) x ∂AddCircle.haarAddCircle) = _
  simp_rw [integral_unitFourier]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, frequencyVector,
    Matrix.cons_val_zero, Matrix.cons_val_succ, mul_one]
  by_cases hx : k.1 = 0 <;> by_cases hy : k.2 = 0 <;>
    simp_all [Prod.ext_iff]

theorem phaseCharacter_integrable (k : ℤ × ℤ) :
    Integrable (phaseCharacter k) HierarchicalLaminates.Periodic.domainMeasure :=
  memLp_one_iff_integrable.mp
    (ContinuousMap.memLp (p := 1) (μ := HierarchicalLaminates.Periodic.domainMeasure) ℂ (phaseCharacter k))

theorem integral_cosineKernel (k : ℤ × ℤ) :
    (∫ x, cosineKernel k x ∂HierarchicalLaminates.Periodic.domainMeasure) =
      if k = (0, 0) then (1 : ℝ) else 0 := by
  change (∫ x, (phaseCharacter k x).re ∂HierarchicalLaminates.Periodic.domainMeasure) = _
  have h := Complex.reCLM.integral_comp_comm (phaseCharacter_integrable k)
  simp only [Complex.reCLM_apply] at h
  rw [h, integral_phaseCharacter]
  by_cases hk : k = (0, 0) <;> simp [hk]

theorem integral_sineKernel (k : ℤ × ℤ) :
    (∫ x, sineKernel k x ∂HierarchicalLaminates.Periodic.domainMeasure) = 0 := by
  change (∫ x, (phaseCharacter k x).im ∂HierarchicalLaminates.Periodic.domainMeasure) = _
  have h := Complex.imCLM.integral_comp_comm (phaseCharacter_integrable k)
  simp only [Complex.imCLM_apply] at h
  rw [h, integral_phaseCharacter]
  by_cases hk : k = (0, 0) <;> simp [hk]

end CharacterIntegrals

theorem uniformMean_cosine_term (k : ℤ × ℤ) (v : E) :
    uniformMean (cosineKernel k • ContinuousMap.const PeriodicDomain v) =
      if k = (0, 0) then v else 0 := by
  rw [uniformMean_eq_integral]
  change (∫ x, cosineKernel k x • v ∂HierarchicalLaminates.Periodic.domainMeasure) = _
  rw [integral_smul_const, integral_cosineKernel]
  by_cases hk : k = (0, 0) <;> simp [hk]

theorem uniformMean_sine_term (k : ℤ × ℤ) (v : E) :
    uniformMean (sineKernel k • ContinuousMap.const PeriodicDomain v) = 0 := by
  rw [uniformMean_eq_integral]
  change (∫ x, sineKernel k x • v ∂HierarchicalLaminates.Periodic.domainMeasure) = _
  rw [integral_smul_const, integral_sineKernel, zero_smul]

theorem cosineSynthesis_mean (f : Coefficients (ℤ × ℤ) E) :
    uniformMean (cosineSynthesis f) = f (0, 0) := by
  unfold cosineSynthesis continuousSynthesis
  rw [uniformMean.map_tsum (synthesisTerm_summable cosineKernel cosineKernel_norm_le f)]
  simp only [synthesisTerm, uniformMean_cosine_term]
  rw [tsum_eq_single (0, 0)]
  · simp
  · intro k hk
    simp [hk]

theorem sineSynthesis_mean (f : Coefficients (ℤ × ℤ) E) :
    uniformMean (sineSynthesis f) = 0 := by
  unfold sineSynthesis continuousSynthesis
  rw [uniformMean.map_tsum (synthesisTerm_summable sineKernel sineKernel_norm_le f)]
  simp only [synthesisTerm, uniformMean_sine_term, tsum_zero]

theorem uniformMean_cosineKernel (k : ℤ × ℤ) :
    uniformMean (cosineKernel k) = if k = (0, 0) then (1 : ℝ) else 0 := by
  rw [uniformMean_eq_integral]
  exact integral_cosineKernel k

theorem cosineProfile_mean_half : uniformMean cosineProfile = (1 / 2 : ℝ) := by
  have hconst : uniformMean (1 : C(PeriodicDomain, ℝ)) = 1 := uniformMean_constant 1
  norm_num [cosineProfile, map_add, map_smul, uniformMean_cosineKernel, hconst]

end HierarchicalLaminates.Fourier
