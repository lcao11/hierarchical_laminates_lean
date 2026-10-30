module

public import HierarchicalLaminates.GClosure.TwoChildIdeal

/-!
# Admissible trial fields for layers of two microscopic patterns
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open MeasureTheory Set HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material
  HierarchicalLaminates.Lamination HierarchicalLaminates.WeakCalculus HierarchicalLaminates.Homogenization HierarchicalLaminates.Composition

def twoChildTrialField (R : TorusCoordinates) (b c : PhaseFraction) (a : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (F : PhysicalGradient) (v₁ v₂ : RegularPotential) : PhysicalField :=
  generalLayerMacroField R a ha (effectiveMatrix b) (effectiveMatrix c) F + v₁.field + v₂.field

def twoChildTrialFlux (R : TorusCoordinates) (b c : PhaseFraction) (a : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (F : PhysicalGradient) (ω₁ ω₂ : RegularPotential) : PhysicalField :=
  generalLayerMacroFlux R a ha (effectiveMatrix b) (effectiveMatrix c) F +
    curlField (ω₁.field + ω₂.field)

theorem twoChildTrialField_admissible (R : TorusCoordinates) (b c : PhaseFraction) (a : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (F : PhysicalGradient) (v₁ v₂ : RegularPotential) :
    twoChildTrialField R b c a ha F v₁ v₂ - constantField F ∈ gradientSpace := by
  have heq : twoChildTrialField R b c a ha F v₁ v₂ - constantField F =
      (generalLayerMacroField R a ha (effectiveMatrix b) (effectiveMatrix c) F - constantField F) +
        v₁.field + v₂.field := by unfold twoChildTrialField; abel
  rw [heq]
  exact gradientSpace.add_mem
    (gradientSpace.add_mem (generalLayerMacroField_admissible R a ha _ _ F) v₁.mem_gradientSpace)
    v₂.mem_gradientSpace

theorem twoChildTrialFlux_orthogonal (R : TorusCoordinates) (b c : PhaseFraction) (a : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (F : PhysicalGradient) (ω₁ ω₂ : RegularPotential)
    (g : PhysicalField) (hg : g ∈ gradientSpace) :
    inner ℝ (twoChildTrialFlux R b c a ha F ω₁ ω₂) g = 0 := by
  rw [twoChildTrialFlux,inner_add_left,generalLayerMacroFlux_orthogonal R a ha _ _ F g hg,
    closedGradient_curl_orthogonal _
      (gradientSpace.add_mem ω₁.mem_gradientSpace ω₂.mem_gradientSpace) g hg,add_zero]

theorem twoChildTrialFlux_mean (R : TorusCoordinates) (b c : PhaseFraction) (a : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (F : PhysicalGradient) (ω₁ ω₂ : RegularPotential) :
    meanField (twoChildTrialFlux R b c a ha F ω₁ ω₂) =
      Matrix.toEuclideanCLM (𝕜 := ℝ)
        (computedLayerTensor (effectiveMatrix b) (effectiveMatrix c) (coordinateNormal R) a) F := by
  rw [twoChildTrialFlux,map_add,closedGradient_curl_mean_zero _
    (gradientSpace.add_mem ω₁.mem_gradientSpace ω₂.mem_gradientSpace),add_zero]
  exact generalLayerMacroFlux_mean R a ha
    (effectiveMatrix_isHermitian b) (effectiveMatrix_isHermitian c) F

theorem twoChildResidual_bound (R : TorusCoordinates) (b c : PhaseFraction)
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) {r₁ k₁ r₂ k₂ : ℕ}
    (hr₁ : 0 < r₁) (hk₁ : 0 < k₁) (hr₂ : 0 < r₂) (hk₂ : 0 < k₂)
    (F : PhysicalGradient) (u₁ ψ₁ u₂ ψ₂ v₁ ω₁ v₂ ω₂ : RegularPotential) :
    ‖twoChildTrialFlux R b c a ⟨ha₀.le,ha₁.le⟩ F ω₁ ω₂ -
      coefficientLaw (twoChildRecovery R b c a r₁ k₁ r₂ k₂)
        (twoChildTrialField R b c a ⟨ha₀.le,ha₁.le⟩ F v₁ v₂)‖ ≤
      ‖regularMicroscopicResidual b (firstChildLoading R b c a F) u₁ ψ₁‖ +
      ‖regularMicroscopicResidual c (secondChildLoading R b c a F) u₂ ψ₂‖ +
      ‖v₁.field - obliqueSlabField R a r₁ k₁ u₁‖ +
      ‖ω₁.field - obliqueSlabField R a r₁ k₁ ψ₁‖ +
      ‖v₂.field - complementarySlabField R a r₂ k₂ u₂‖ +
      ‖ω₂.field - complementarySlabField R a r₂ k₂ ψ₂‖ := by
  have h := residual_transfer_bound (twoChildRecovery R b c a r₁ k₁ r₂ k₂)
    (twoChildTrialField R b c a ⟨ha₀.le,ha₁.le⟩ F v₁ v₂)
    (twoChildTrialFlux R b c a ⟨ha₀.le,ha₁.le⟩ F ω₁ ω₂)
    (twoChildIdealField R b c a ⟨ha₀.le,ha₁.le⟩ r₁ k₁ r₂ k₂ F u₁ u₂)
    (twoChildIdealFlux R b c a ⟨ha₀.le,ha₁.le⟩ r₁ k₁ r₂ k₂ F ψ₁ ψ₂)
  have he : twoChildTrialField R b c a ⟨ha₀.le,ha₁.le⟩ F v₁ v₂ -
      twoChildIdealField R b c a ⟨ha₀.le,ha₁.le⟩ r₁ k₁ r₂ k₂ F u₁ u₂ =
      (v₁.field - obliqueSlabField R a r₁ k₁ u₁) +
        (v₂.field - complementarySlabField R a r₂ k₂ u₂) := by
    unfold twoChildTrialField twoChildIdealField
    abel
  have hj : twoChildTrialFlux R b c a ⟨ha₀.le,ha₁.le⟩ F ω₁ ω₂ -
      twoChildIdealFlux R b c a ⟨ha₀.le,ha₁.le⟩ r₁ k₁ r₂ k₂ F ψ₁ ψ₂ =
      curlField ((ω₁.field - obliqueSlabField R a r₁ k₁ ψ₁) +
        (ω₂.field - complementarySlabField R a r₂ k₂ ψ₂)) := by
    unfold twoChildTrialFlux twoChildIdealFlux
    simp only [map_add,map_sub]
    abel
  rw [he,hj,curlField_norm] at h
  have hE := norm_add_le (v₁.field - obliqueSlabField R a r₁ k₁ u₁)
    (v₂.field - complementarySlabField R a r₂ k₂ u₂)
  have hJ := norm_add_le (ω₁.field - obliqueSlabField R a r₁ k₁ ψ₁)
    (ω₂.field - complementarySlabField R a r₂ k₂ ψ₂)
  have hI := twoChildIdealResidual_norm_le R b c a ha₀ ha₁ hr₁ hk₁ hr₂ hk₂ F u₁ ψ₁ u₂ ψ₂
  linarith

theorem twoChild_response_error_bound (R : TorusCoordinates) (b c : PhaseFraction)
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) {r₁ k₁ r₂ k₂ : ℕ}
    (hr₁ : 0 < r₁) (hk₁ : 0 < k₁) (hr₂ : 0 < r₂) (hk₂ : 0 < k₂)
    (F : PhysicalGradient) (u₁ ψ₁ u₂ ψ₂ v₁ ω₁ v₂ ω₂ : RegularPotential) :
    ‖HierarchicalLaminates.Material.effectiveOperator (twoChildRecovery R b c a r₁ k₁ r₂ k₂) F -
      Matrix.toEuclideanCLM (𝕜 := ℝ)
        (computedLayerTensor (effectiveMatrix b) (effectiveMatrix c) (coordinateNormal R) a) F‖ ≤
      5 * (‖regularMicroscopicResidual b (firstChildLoading R b c a F) u₁ ψ₁‖ +
      ‖regularMicroscopicResidual c (secondChildLoading R b c a F) u₂ ψ₂‖ +
      ‖v₁.field - obliqueSlabField R a r₁ k₁ u₁‖ +
      ‖ω₁.field - obliqueSlabField R a r₁ k₁ ψ₁‖ +
      ‖v₂.field - complementarySlabField R a r₂ k₂ u₂‖ +
      ‖ω₂.field - complementarySlabField R a r₂ k₂ ψ₂‖) := by
  have h := trial_response_error (twoChildRecovery R b c a r₁ k₁ r₂ k₂) F
    (twoChildTrialField R b c a ⟨ha₀.le,ha₁.le⟩ F v₁ v₂)
    (twoChildTrialFlux R b c a ⟨ha₀.le,ha₁.le⟩ F ω₁ ω₂)
    (twoChildTrialField_admissible R b c a ⟨ha₀.le,ha₁.le⟩ F v₁ v₂)
    (twoChildTrialFlux_orthogonal R b c a ⟨ha₀.le,ha₁.le⟩ F ω₁ ω₂)
  rw [twoChildTrialFlux_mean R b c a ⟨ha₀.le,ha₁.le⟩ F ω₁ ω₂] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (twoChildResidual_bound R b c a ha₀ ha₁ hr₁ hk₁ hr₂ hk₂ F u₁ ψ₁ u₂ ψ₂ v₁ ω₁ v₂ ω₂)
    (by norm_num))

end HierarchicalLaminates.GClosure
