module

public import HierarchicalLaminates.Fourier.IntegrationByParts

/-!
# Divergence-free cosine fluxes annihilate weak gradients

The distributional derivative identity gives orthogonality to the periodic
H¹ gradient space and its L² closure.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Fourier

open MeasureTheory
open HierarchicalLaminates.Periodic

def cosineMoment (k : HierarchicalLaminates.Frequency) (g : PhysicalField) : PhysicalGradient :=
  ∫ q, cosineKernel k q • g q ∂domainMeasure

theorem cosineMoment_integrable (k : HierarchicalLaminates.Frequency) (g : PhysicalField) :
    Integrable (fun q => cosineKernel k q • g q) domainMeasure := by
  have hbound : ∀ᵐ q ∂domainMeasure, ‖cosineKernel k q‖ ≤ 1 := by
    exact Filter.Eventually.of_forall (fun q => by
      simpa only [Real.norm_eq_abs] using cosineKernel_abs_le k q)
  exact (field_integrable g).bdd_smul (φ := fun q => cosineKernel k q) 1
    (cosineKernel k).continuous.aestronglyMeasurable hbound

theorem cosineMoment_component (k : HierarchicalLaminates.Frequency) (g : PhysicalField)
    (i : Fin 2) (a : Fin 16) :
    cosineMoment k g (i, a) =
      inner ℝ (componentField i a g) (continuousField (cosineKernel k)) := by
  have hproj := (EuclideanSpace.proj (𝕜 := ℝ) (i, a)).integral_comp_comm
    (cosineMoment_integrable k g)
  change (∫ q, (EuclideanSpace.proj (𝕜 := ℝ) (i, a))
    (cosineKernel k q • g q) ∂domainMeasure) = cosineMoment k g (i, a) at hproj
  rw [← hproj, L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [(EuclideanSpace.proj (𝕜 := ℝ) (i, a)).coeFn_compLpL g,
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure (cosineKernel k)]
      with q hcomp hcos
  change (EuclideanSpace.proj (𝕜 := ℝ) (i, a)) (cosineKernel k q • g q) =
    inner ℝ ((EuclideanSpace.proj (𝕜 := ℝ) (i, a)).compLpL 2 domainMeasure g q)
      (ContinuousMap.toLp 2 domainMeasure ℝ (cosineKernel k) q)
  rw [hcomp, hcos, map_smul]
  simp only [Real.inner_apply, smul_eq_mul, mul_comm]

theorem cosineMode_pairing (k : HierarchicalLaminates.Frequency) (v : PhysicalGradient)
    (g : PhysicalField) :
    inner ℝ (continuousField (cosineKernel k • ContinuousMap.const PeriodicDomain v)) g =
      inner ℝ v (cosineMoment k g) := by
  have hint := (innerSL ℝ v).integral_comp_comm (cosineMoment_integrable k g)
  rw [L2.inner_def]
  change _ = (innerSL ℝ v) (∫ q, cosineKernel k q • g q ∂domainMeasure)
  rw [← hint]
  apply integral_congr_ae
  filter_upwards
    [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure
      (cosineKernel k • ContinuousMap.const PeriodicDomain v)] with q hcos
  change inner ℝ (ContinuousMap.toLp 2 domainMeasure ℝ
    (cosineKernel k • ContinuousMap.const PeriodicDomain v) q) (g q) = _
  rw [hcos]
  simp only [ContinuousMap.smul_apply', ContinuousMap.const_apply,
    innerSL_apply_apply, real_inner_smul_left, inner_smul_right]

theorem weakGradient_cosineMoment {u : Fin 16 → ScalarField} {g : PhysicalField}
    (hu : HasWeakGradient u g) (k : HierarchicalLaminates.Frequency) (i : Fin 2) (a : Fin 16) :
    cosineMoment k g (i, a) = angularFrequency k i *
      inner ℝ (u a) (continuousField (sineKernel k)) := by
  rw [cosineMoment_component]
  have h := hu i a (cosineTest k)
  simpa only [cosineTest, map_smul, inner_smul_right, angularFrequency,
    neg_mul, neg_neg] using h

theorem cosineMode_weakGradient_zero
    (k : HierarchicalLaminates.Frequency) (v : PhysicalGradient)
    (hdiv : ∀ a : Fin 16, ∑ i : Fin 2, angularFrequency k i * v (i, a) = 0)
    {u : Fin 16 → ScalarField} {g : PhysicalField} (hu : HasWeakGradient u g) :
    inner ℝ (continuousField (cosineKernel k • ContinuousMap.const PeriodicDomain v)) g = 0 := by
  rw [cosineMode_pairing, PiLp.inner_apply]
  simp only [Real.inner_apply]
  change (∑ c : Fin 2 × Fin 16, v c * cosineMoment k g c) = 0
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro a _
  simp_rw [weakGradient_cosineMoment hu]
  calc
    (∑ i : Fin 2, v (i, a) * (angularFrequency k i *
        inner ℝ (u a) (continuousField (sineKernel k)))) =
        (∑ i : Fin 2, angularFrequency k i * v (i, a)) *
          inner ℝ (u a) (continuousField (sineKernel k)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [hdiv a, zero_mul]

theorem cosineMode_gradient_zero
    (k : HierarchicalLaminates.Frequency) (v : PhysicalGradient)
    (hdiv : ∀ a : Fin 16, ∑ i : Fin 2, angularFrequency k i * v (i, a) = 0)
    (g : PhysicalField) (hg : g ∈ gradientSpace) :
    inner ℝ (continuousField (cosineKernel k • ContinuousMap.const PeriodicDomain v)) g = 0 := by
  let L : PhysicalField →L[ℝ] ℝ :=
    innerSL ℝ (continuousField (cosineKernel k • ContinuousMap.const PeriodicDomain v))
  have hweak : weakGradientSpace ≤ L.ker := by
    intro w hw
    rcases hw with ⟨u, hu⟩
    exact cosineMode_weakGradient_zero k v hdiv hu
  have hclosed : gradientSpace ≤ L.ker :=
    weakGradientSpace.topologicalClosure_minimal hweak L.isClosed_ker
  exact hclosed hg

theorem cosineSynthesis_gradient_zero
    (v : Coefficients HierarchicalLaminates.Frequency PhysicalGradient)
    (hdiv : ∀ (k : HierarchicalLaminates.Frequency) (a : Fin 16),
      ∑ i : Fin 2, angularFrequency k i * v k (i, a) = 0)
    (g : PhysicalField) (hg : g ∈ gradientSpace) :
    inner ℝ (continuousField (cosineSynthesis v)) g = 0 := by
  let L : C(PeriodicDomain, PhysicalGradient) →L[ℝ] ℝ :=
    (innerSL ℝ g).comp continuousField
  have hsum : Summable (synthesisTerm cosineKernel v) :=
    synthesisTerm_summable cosineKernel cosineKernel_norm_le v
  have hmap := L.map_tsum hsum
  change inner ℝ g (continuousField (cosineSynthesis v)) = _ at hmap
  rw [real_inner_comm] at hmap
  rw [hmap]
  have hz : ∀ k, L (synthesisTerm cosineKernel v k) = 0 := by
    intro k
    change inner ℝ g (continuousField
      (cosineKernel k • ContinuousMap.const PeriodicDomain (v k))) = 0
    rw [real_inner_comm]
    exact cosineMode_gradient_zero k (v k) (hdiv k) g hg
  simp only [hz, tsum_zero]

theorem cosineSynthesis_gradient_zero_of_frequency
    (v : Coefficients HierarchicalLaminates.Frequency PhysicalGradient)
    (hdiv : ∀ (k : HierarchicalLaminates.Frequency) (a : Fin 16),
      (k.1 : ℝ) * v k (0, a) + (k.2 : ℝ) * v k (1, a) = 0)
    (g : PhysicalField) (hg : g ∈ gradientSpace) :
    inner ℝ (continuousField (cosineSynthesis v)) g = 0 := by
  apply cosineSynthesis_gradient_zero v _ g hg
  intro k a
  norm_num [Fin.sum_univ_succ, angularFrequency, frequencyVector]
  change 2 * Real.pi * (k.1 : ℝ) * v k (0, a) +
    2 * Real.pi * (k.2 : ℝ) * v k (1, a) = 0
  have h := hdiv k a
  linear_combination (2 * Real.pi) * h

end HierarchicalLaminates.Fourier
