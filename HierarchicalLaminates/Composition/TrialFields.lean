module

public import HierarchicalLaminates.Composition.IdealResidual
public import HierarchicalLaminates.Composition.LocalizedPotential
public import HierarchicalLaminates.Composition.CurlNorm

/-!
# Admissible recovery fields and their constitutive residual
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.Composition

open HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material HierarchicalLaminates.WeakCalculus HierarchicalLaminates.Homogenization

def recoveryTrialField (θ δ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hδ : 0 < δ)
    (r : ℕ) (hr : 0 < r) (k : ℕ) (F : PhysicalGradient) (u : RegularPotential) : PhysicalField :=
  constantField F +
    (localizedPotential (layerFraction_pos hθ₀ hθ₁) (layerFraction_le_one θ) hδ hr k u).field

def recoveryTrialFlux (b : PhaseFraction) (θ δ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hδ : 0 < δ) (r : ℕ) (hr : 0 < r) (k : ℕ) (F : PhysicalGradient)
    (ψ : RegularPotential) : PhysicalField :=
  seedMacroFlux b θ hθ₀ hθ₁ F + curlField
    (localizedPotential (layerFraction_pos hθ₀ hθ₁) (layerFraction_le_one θ) hδ hr k ψ).field

theorem recoveryTrialField_admissible (θ δ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hδ : 0 < δ) (r : ℕ) (hr : 0 < r) (k : ℕ) (F : PhysicalGradient)
    (u : RegularPotential) :
    recoveryTrialField θ δ hθ₀ hθ₁ hδ r hr k F u - constantField F ∈ gradientSpace := by
  unfold recoveryTrialField
  simpa only [add_sub_cancel_left] using
    (localizedPotential (layerFraction_pos hθ₀ hθ₁) (layerFraction_le_one θ) hδ hr k u).mem_gradientSpace

theorem recoveryTrialFlux_orthogonal (b : PhaseFraction) (θ δ : ℝ)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hδ : 0 < δ) (r : ℕ) (hr : 0 < r)
    (k : ℕ) (F : PhysicalGradient) (ψ : RegularPotential)
    (g : PhysicalField) (hg : g ∈ gradientSpace) :
    inner ℝ (recoveryTrialFlux b θ δ hθ₀ hθ₁ hδ r hr k F ψ) g = 0 := by
  rw [recoveryTrialFlux, inner_add_left, seedMacroFlux_orthogonal b θ hθ₀ hθ₁ F g hg,
    RegularPotential.curl_orthogonal _ g hg, add_zero]

theorem recoveryTrialFlux_mean (b : PhaseFraction) (θ δ : ℝ)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hδ : 0 < δ) (r : ℕ) (hr : 0 < r)
    (k : ℕ) (F : PhysicalGradient) (ψ : RegularPotential) :
    meanField (recoveryTrialFlux b θ δ hθ₀ hθ₁ hδ r hr k F ψ) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (arithmeticCandidate θ (effectiveMatrix b)) F := by
  rw [recoveryTrialFlux, map_add, RegularPotential.curl_mean_zero, add_zero,
    seedMacroFlux_mean]

theorem recoveryTrialResidual_bound (b : PhaseFraction) (θ δ : ℝ)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hδ : 0 < δ) (r : ℕ) (hr : 0 < r)
    (k : ℕ) (hk : 0 < k) (F : PhysicalGradient) (u ψ : RegularPotential) :
    ‖recoveryTrialFlux b θ δ hθ₀ hθ₁ hδ r hr k F ψ -
      coefficientLaw (thetaRecovery b θ r k) (recoveryTrialField θ δ hθ₀ hθ₁ hδ r hr k F u)‖ ≤
      ‖regularMicroscopicResidual b F u ψ‖ +
      ‖(localizedPotential (layerFraction_pos hθ₀ hθ₁) (layerFraction_le_one θ) hδ hr k u).field -
        u.slabField (layerFraction θ) r k‖ +
      ‖(localizedPotential (layerFraction_pos hθ₀ hθ₁) (layerFraction_le_one θ) hδ hr k ψ).field -
        ψ.slabField (layerFraction θ) r k‖ := by
  have h := residual_transfer_bound (thetaRecovery b θ r k)
    (recoveryTrialField θ δ hθ₀ hθ₁ hδ r hr k F u)
    (recoveryTrialFlux b θ δ hθ₀ hθ₁ hδ r hr k F ψ)
    (idealTrialField (layerFraction θ) r k F u)
    (idealTrialFlux b θ hθ₀ hθ₁ r k F ψ)
  have he : recoveryTrialField θ δ hθ₀ hθ₁ hδ r hr k F u -
      idealTrialField (layerFraction θ) r k F u =
      (localizedPotential (layerFraction_pos hθ₀ hθ₁) (layerFraction_le_one θ) hδ hr k u).field -
        u.slabField (layerFraction θ) r k := by
    unfold recoveryTrialField idealTrialField
    abel
  have hj : recoveryTrialFlux b θ δ hθ₀ hθ₁ hδ r hr k F ψ -
      idealTrialFlux b θ hθ₀ hθ₁ r k F ψ = curlField
      ((localizedPotential (layerFraction_pos hθ₀ hθ₁) (layerFraction_le_one θ) hδ hr k ψ).field -
        ψ.slabField (layerFraction θ) r k) := by
    unfold recoveryTrialFlux idealTrialFlux
    rw [map_sub]
    abel
  rw [he, hj, curlField_norm] at h
  have hideal := idealResidual_norm_le b θ hθ₀ hθ₁ hr hk F u ψ
  linarith

theorem recovery_response_error_bound (b : PhaseFraction) (θ δ : ℝ)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hδ : 0 < δ) (r : ℕ) (hr : 0 < r)
    (k : ℕ) (hk : 0 < k) (F : PhysicalGradient) (u ψ : RegularPotential) :
    ‖HierarchicalLaminates.Material.effectiveOperator (thetaRecovery b θ r k) F -
      Matrix.toEuclideanCLM (𝕜 := ℝ) (arithmeticCandidate θ (effectiveMatrix b)) F‖ ≤
      5 * (‖regularMicroscopicResidual b F u ψ‖ +
      ‖(localizedPotential (layerFraction_pos hθ₀ hθ₁) (layerFraction_le_one θ) hδ hr k u).field -
        u.slabField (layerFraction θ) r k‖ +
      ‖(localizedPotential (layerFraction_pos hθ₀ hθ₁) (layerFraction_le_one θ) hδ hr k ψ).field -
        ψ.slabField (layerFraction θ) r k‖) := by
  have h := trial_response_error (thetaRecovery b θ r k) F
    (recoveryTrialField θ δ hθ₀ hθ₁ hδ r hr k F u)
    (recoveryTrialFlux b θ δ hθ₀ hθ₁ hδ r hr k F ψ)
    (recoveryTrialField_admissible θ δ hθ₀ hθ₁ hδ r hr k F u)
    (recoveryTrialFlux_orthogonal b θ δ hθ₀ hθ₁ hδ r hr k F ψ)
  rw [recoveryTrialFlux_mean] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (recoveryTrialResidual_bound b θ δ hθ₀ hθ₁ hδ r hr k hk F u ψ) (by norm_num))

end HierarchicalLaminates.Composition
