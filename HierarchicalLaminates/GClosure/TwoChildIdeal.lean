module

public import HierarchicalLaminates.GClosure.TwoChildResidualValues
public import HierarchicalLaminates.GClosure.ObliqueComplement

/-! The ideal two-child constitutive residual is the sum of the transported child residuals. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open MeasureTheory Set HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material
  HierarchicalLaminates.Lamination HierarchicalLaminates.WeakCalculus HierarchicalLaminates.Binary HierarchicalLaminates.Homogenization
  HierarchicalLaminates.Composition

theorem firstSlab_coe (R : TorusCoordinates) (a : ℝ) (r k : ℕ) (u : RegularPotential) :
    obliqueSlabField R a r k u =ᵐ[domainMeasure] firstMicroValue R a r k u.gradient :=
  obliqueSlabField_coe R a r k u

theorem secondSlab_coe (R : TorusCoordinates) (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1)
    (r k : ℕ) (u : RegularPotential) :
    complementarySlabField R a r k u =ᵐ[domainMeasure] secondMicroValue R a r k u.gradient := by
  filter_upwards [complementarySlabField_coe R a ha₀ ha₁ r k u] with q hq
  by_cases h : coordinateRepresentative 1 (R.equiv q) < a
  · simpa [secondMicroValue,h,not_le_of_gt h] using hq
  · simpa [secondMicroValue,h,le_of_not_gt h] using hq

def twoChildIdealField (R : TorusCoordinates) (b c : PhaseFraction) (a : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (r₁ k₁ r₂ k₂ : ℕ) (F : PhysicalGradient)
    (u₁ u₂ : RegularPotential) : PhysicalField :=
  generalLayerMacroField R a ha (effectiveMatrix b) (effectiveMatrix c) F +
    obliqueSlabField R a r₁ k₁ u₁ + complementarySlabField R a r₂ k₂ u₂

def twoChildIdealFlux (R : TorusCoordinates) (b c : PhaseFraction) (a : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (r₁ k₁ r₂ k₂ : ℕ) (F : PhysicalGradient)
    (ψ₁ ψ₂ : RegularPotential) : PhysicalField :=
  generalLayerMacroFlux R a ha (effectiveMatrix b) (effectiveMatrix c) F +
    curlField (obliqueSlabField R a r₁ k₁ ψ₁ + complementarySlabField R a r₂ k₂ ψ₂)

def firstChildResidual (R : TorusCoordinates) (b c : PhaseFraction) (a : ℝ)
    (r k : ℕ) (F : PhysicalGradient) (u ψ : RegularPotential) : PhysicalField :=
  obliqueSlabPhysicalField R a r k
    (regularMicroscopicResidualValue b (firstChildLoading R b c a F) u ψ)
    (regularMicroscopicResidualValue_measurable _ _ _ _)
    (regularMicroscopicResidualBound _ _ _ _) (regularMicroscopicResidualBound_nonneg _ _ _ _)
    (regularMicroscopicResidualValue_bound _ _ _ _)

def secondChildResidual (R : TorusCoordinates) (b c : PhaseFraction) (a : ℝ)
    (r k : ℕ) (F : PhysicalGradient) (u ψ : RegularPotential) : PhysicalField :=
  complementarySlabPhysicalField R a r k
    (regularMicroscopicResidualValue c (secondChildLoading R b c a F) u ψ)
    (regularMicroscopicResidualValue_measurable _ _ _ _)
    (regularMicroscopicResidualBound _ _ _ _) (regularMicroscopicResidualBound_nonneg _ _ _ _)
    (regularMicroscopicResidualValue_bound _ _ _ _)

theorem firstChildResidual_coe (R : TorusCoordinates) (b c : PhaseFraction) (a : ℝ)
    (r k : ℕ) (F : PhysicalGradient) (u ψ : RegularPotential) :
    firstChildResidual R b c a r k F u ψ =ᵐ[domainMeasure]
      firstMicroValue R a r k (regularMicroscopicResidualValue b (firstChildLoading R b c a F) u ψ) :=
  obliqueSlabPhysicalField_coe _ _ _ _ _ _ _ _ _

theorem secondChildResidual_coe (R : TorusCoordinates) (b c : PhaseFraction) (a : ℝ)
    (ha₀ : 0 < a) (ha₁ : a < 1) (r k : ℕ) (F : PhysicalGradient) (u ψ : RegularPotential) :
    secondChildResidual R b c a r k F u ψ =ᵐ[domainMeasure]
      secondMicroValue R a r k (regularMicroscopicResidualValue c (secondChildLoading R b c a F) u ψ) := by
  unfold secondChildResidual
  filter_upwards [complementarySlabPhysicalField_coe R a ha₀ ha₁ r k
      (regularMicroscopicResidualValue c (secondChildLoading R b c a F) u ψ)
      (regularMicroscopicResidualValue_measurable _ _ _ _) (regularMicroscopicResidualBound _ _ _ _)
      (regularMicroscopicResidualBound_nonneg _ _ _ _) (regularMicroscopicResidualValue_bound _ _ _ _)]
    with q hq
  by_cases h : coordinateRepresentative 1 (R.equiv q) < a
  · simpa [secondMicroValue,h,not_le_of_gt h] using hq
  · simpa [secondMicroValue,h,le_of_not_gt h] using hq

theorem firstChildResidual_norm_le (R : TorusCoordinates) (b c : PhaseFraction) (a : ℝ)
    (ha : a ∈ Ioc (0 : ℝ) 1) {r k : ℕ} (hr : 0 < r) (hk : 0 < k)
    (F : PhysicalGradient) (u ψ : RegularPotential) :
    ‖firstChildResidual R b c a r k F u ψ‖ ≤
      ‖regularMicroscopicResidual b (firstChildLoading R b c a F) u ψ‖ := by
  rw [regularMicroscopicResidual_eq_bounded]
  exact obliqueSlabPhysicalField_norm_le R ha hr hk _ _ _ _ _

theorem secondChildResidual_norm_le (R : TorusCoordinates) (b c : PhaseFraction) (a : ℝ)
    (ha₀ : 0 < a) (ha₁ : a < 1) {r k : ℕ} (hr : 0 < r) (hk : 0 < k)
    (F : PhysicalGradient) (u ψ : RegularPotential) :
    ‖secondChildResidual R b c a r k F u ψ‖ ≤
      ‖regularMicroscopicResidual c (secondChildLoading R b c a F) u ψ‖ := by
  rw [regularMicroscopicResidual_eq_bounded]
  exact complementarySlabPhysicalField_norm_le R a ha₀ ha₁ hr hk _ _ _ _ _

theorem twoChildIdealResidual_eq (R : TorusCoordinates) (b c : PhaseFraction)
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (r₁ k₁ r₂ k₂ : ℕ)
    (F : PhysicalGradient) (u₁ ψ₁ u₂ ψ₂ : RegularPotential) :
    twoChildIdealFlux R b c a ⟨ha₀.le,ha₁.le⟩ r₁ k₁ r₂ k₂ F ψ₁ ψ₂ -
      coefficientLaw (twoChildRecovery R b c a r₁ k₁ r₂ k₂)
        (twoChildIdealField R b c a ⟨ha₀.le,ha₁.le⟩ r₁ k₁ r₂ k₂ F u₁ u₂) =
      firstChildResidual R b c a r₁ k₁ F u₁ ψ₁ + secondChildResidual R b c a r₂ k₂ F u₂ ψ₂ := by
  apply residual_eq_of_ae
  · exact physicalField_add_coe
      (physicalField_add_coe (twoChildMacroField_coe R b c a ⟨ha₀.le,ha₁.le⟩ F)
        (firstSlab_coe R a r₁ k₁ u₁)) (secondSlab_coe R a ha₀ ha₁ r₂ k₂ u₂)
  · exact physicalField_add_coe (twoChildMacroFlux_coe R b c a ⟨ha₀.le,ha₁.le⟩ F)
      (curlPhysicalField_coe (physicalField_add_coe (firstSlab_coe R a r₁ k₁ ψ₁)
        (secondSlab_coe R a ha₀ ha₁ r₂ k₂ ψ₂)))
  · exact physicalField_add_coe (firstChildResidual_coe R b c a r₁ k₁ F u₁ ψ₁)
      (secondChildResidual_coe R b c a ha₀ ha₁ r₂ k₂ F u₂ ψ₂)
  · exact twoChildResidualValue_eq R b c a r₁ k₁ r₂ k₂ F u₁ ψ₁ u₂ ψ₂

theorem twoChildIdealResidual_norm_le (R : TorusCoordinates) (b c : PhaseFraction)
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) {r₁ k₁ r₂ k₂ : ℕ}
    (hr₁ : 0 < r₁) (hk₁ : 0 < k₁) (hr₂ : 0 < r₂) (hk₂ : 0 < k₂)
    (F : PhysicalGradient) (u₁ ψ₁ u₂ ψ₂ : RegularPotential) :
    ‖twoChildIdealFlux R b c a ⟨ha₀.le,ha₁.le⟩ r₁ k₁ r₂ k₂ F ψ₁ ψ₂ -
      coefficientLaw (twoChildRecovery R b c a r₁ k₁ r₂ k₂)
        (twoChildIdealField R b c a ⟨ha₀.le,ha₁.le⟩ r₁ k₁ r₂ k₂ F u₁ u₂)‖ ≤
      ‖regularMicroscopicResidual b (firstChildLoading R b c a F) u₁ ψ₁‖ +
        ‖regularMicroscopicResidual c (secondChildLoading R b c a F) u₂ ψ₂‖ := by
  rw [twoChildIdealResidual_eq R b c a ha₀ ha₁]
  exact (norm_add_le _ _).trans (add_le_add
    (firstChildResidual_norm_le R b c a ⟨ha₀,ha₁.le⟩ hr₁ hk₁ F u₁ ψ₁)
    (secondChildResidual_norm_le R b c a ha₀ ha₁ hr₂ hk₂ F u₂ ψ₂))

end HierarchicalLaminates.GClosure
