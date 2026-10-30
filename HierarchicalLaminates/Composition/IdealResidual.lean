module

public import HierarchicalLaminates.Composition.MicroscopicApproximation
public import HierarchicalLaminates.Composition.SlabIntegrals
public import HierarchicalLaminates.Composition.MacroFlux

/-! The exact residual of microscopic trial fields transported into a slab. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.Composition

open MeasureTheory HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material
  HierarchicalLaminates.WeakCalculus HierarchicalLaminates.Binary HierarchicalLaminates.Homogenization

def RegularPotential.slabField (a : ℝ) (r k : ℕ) (u : RegularPotential) : PhysicalField :=
  slabPhysicalField a r k u.gradient u.gradient.continuous.measurable ‖u.gradient‖
    (norm_nonneg _) u.gradient.norm_coe_le_norm

theorem RegularPotential.slabField_coe (a : ℝ) (r k : ℕ) (u : RegularPotential) :
    u.slabField a r k =ᵐ[domainMeasure] slabPhysicalValue a r k u.gradient :=
  slabPhysicalField_coe _ _ _ _ _ _ _ _

def regularMicroscopicResidualValue (b : PhaseFraction) (F : PhysicalGradient)
    (u ψ : RegularPotential) (q : Domain) : PhysicalGradient :=
  HierarchicalLaminates.Material.effectiveOperator b F + curlOperator (ψ.gradient q) -
    coefficientOperator b q (F + u.gradient q)

theorem regularMicroscopicResidualValue_measurable (b : PhaseFraction) (F : PhysicalGradient)
    (u ψ : RegularPotential) : Measurable (regularMicroscopicResidualValue b F u ψ) := by
  have he : Measurable (fun q : Domain => F + u.gradient q) :=
    measurable_const.add u.gradient.continuous.measurable
  have hA : Measurable (fun q : Domain => coefficientOperator b q (F + u.gradient q)) := by
    change Measurable (fun q : Domain => zeroPhaseOperator (F + u.gradient q) +
      b.value q • (onePhaseOperator - zeroPhaseOperator) (F + u.gradient q))
    exact (zeroPhaseOperator.continuous.measurable.comp he).add
      (b.measurable.smul ((onePhaseOperator - zeroPhaseOperator).continuous.measurable.comp he))
  exact (measurable_const.add (curlOperator.continuous.measurable.comp
    ψ.gradient.continuous.measurable)).sub hA

def regularMicroscopicResidualBound (b : PhaseFraction) (F : PhysicalGradient)
    (u ψ : RegularPotential) : ℝ :=
  ‖HierarchicalLaminates.Material.effectiveOperator b F‖ + ‖curlOperator‖ * ‖ψ.gradient‖ +
    (‖F‖ + ‖u.gradient‖)

theorem regularMicroscopicResidualBound_nonneg (b : PhaseFraction) (F : PhysicalGradient)
    (u ψ : RegularPotential) : 0 ≤ regularMicroscopicResidualBound b F u ψ := by
  unfold regularMicroscopicResidualBound
  positivity

theorem regularMicroscopicResidualValue_bound (b : PhaseFraction) (F : PhysicalGradient)
    (u ψ : RegularPotential) (q : Domain) :
    ‖regularMicroscopicResidualValue b F u ψ q‖ ≤ regularMicroscopicResidualBound b F u ψ := by
  have hc := (curlOperator.le_opNorm (ψ.gradient q)).trans
    (mul_le_mul_of_nonneg_left (ψ.gradient.norm_coe_le_norm q) (norm_nonneg _))
  have he := (coefficientOperator_bound b q (F + u.gradient q)).trans
    ((by simpa only [one_mul] using norm_add_le F (u.gradient q)) :
      1 * ‖F + u.gradient q‖ ≤ ‖F‖ + ‖u.gradient q‖)
  have he' : ‖coefficientOperator b q (F + u.gradient q)‖ ≤ ‖F‖ + ‖u.gradient‖ :=
    he.trans (add_le_add le_rfl (u.gradient.norm_coe_le_norm q))
  unfold regularMicroscopicResidualValue regularMicroscopicResidualBound
  exact (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add le_rfl hc)) he')

theorem regularMicroscopicResidual_coe (b : PhaseFraction) (F : PhysicalGradient)
    (u ψ : RegularPotential) : regularMicroscopicResidual b F u ψ =ᵐ[domainMeasure]
      regularMicroscopicResidualValue b F u ψ := by
  filter_upwards [Lp.coeFn_sub
      (constantField (HierarchicalLaminates.Material.effectiveOperator b F) + curlField ψ.field)
      (coefficientLaw b (constantField F + u.field)),
    Lp.coeFn_add (constantField (HierarchicalLaminates.Material.effectiveOperator b F)) (curlField ψ.field),
    Lp.coeFn_const 2 domainMeasure (HierarchicalLaminates.Material.effectiveOperator b F),
    curlOperator.coeFn_compLpL ψ.field,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure ψ.gradient,
    coefficientLaw_coe b (constantField F + u.field),
    Lp.coeFn_add (constantField F) u.field,
    Lp.coeFn_const 2 domainMeasure F,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure u.gradient]
      with q hsub hadd hc hcurl hψ hA he hF hu
  change ψ.field q = _ at hψ
  change u.field q = _ at hu
  change curlField ψ.field q = _ at hcurl
  change constantField F q = _ at hF
  change constantField (HierarchicalLaminates.Material.effectiveOperator b F) q = _ at hc
  change (constantField (HierarchicalLaminates.Material.effectiveOperator b F) + curlField ψ.field -
    coefficientLaw b (constantField F + u.field)) q = _
  rw [hsub]
  simp only [Pi.sub_apply, Pi.add_apply] at hadd he ⊢
  rw [hadd, hc, hcurl, hψ, hA, he, hF, hu]
  rfl

theorem regularMicroscopicResidual_eq_bounded (b : PhaseFraction) (F : PhysicalGradient)
    (u ψ : RegularPotential) :
    regularMicroscopicResidual b F u ψ = boundedPhysicalField
      (regularMicroscopicResidualValue b F u ψ)
      (regularMicroscopicResidualValue_measurable b F u ψ)
      (regularMicroscopicResidualBound b F u ψ) (regularMicroscopicResidualValue_bound b F u ψ) := by
  apply Lp.ext
  exact (regularMicroscopicResidual_coe b F u ψ).trans
    (boundedPhysicalField_coe _ _ _ _).symm

def idealTrialField (a : ℝ) (r k : ℕ) (F : PhysicalGradient) (u : RegularPotential) : PhysicalField :=
  constantField F + u.slabField a r k

def idealTrialFlux (b : PhaseFraction) (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (r k : ℕ) (F : PhysicalGradient) (ψ : RegularPotential) : PhysicalField :=
  seedMacroFlux b θ hθ₀ hθ₁ F + curlField (ψ.slabField (layerFraction θ) r k)

def slabMicroscopicResidual (b : PhaseFraction) (θ : ℝ) (r k : ℕ)
    (F : PhysicalGradient) (u ψ : RegularPotential) : PhysicalField :=
  slabPhysicalField (layerFraction θ) r k (regularMicroscopicResidualValue b F u ψ)
    (regularMicroscopicResidualValue_measurable b F u ψ)
    (regularMicroscopicResidualBound b F u ψ) (regularMicroscopicResidualBound_nonneg b F u ψ)
    (regularMicroscopicResidualValue_bound b F u ψ)

theorem slabMicroscopicResidual_norm_le (b : PhaseFraction) {θ : ℝ}
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) {r k : ℕ} (hr : 0 < r) (hk : 0 < k)
    (F : PhysicalGradient) (u ψ : RegularPotential) :
    ‖slabMicroscopicResidual b θ r k F u ψ‖ ≤ ‖regularMicroscopicResidual b F u ψ‖ := by
  rw [regularMicroscopicResidual_eq_bounded b F u ψ]
  exact slabPhysicalField_norm_le ⟨layerFraction_pos hθ₀ hθ₁, layerFraction_le_one θ⟩
    hr hk _ _ _ _ _

theorem idealResidualValue_eq (b : PhaseFraction) (θ : ℝ) (r k : ℕ)
    (F : PhysicalGradient) (u ψ : RegularPotential) (q : Domain) :
    (if coordinateRepresentative 1 q < layerFraction θ then
      HierarchicalLaminates.Material.effectiveOperator b F
    else Matrix.toEuclideanCLM (𝕜 := ℝ) (pureTensor θ) F) +
      curlOperator (slabPhysicalValue (layerFraction θ) r k ψ.gradient q) -
      coefficientOperator (thetaRecovery b θ r k) q
        (F + slabPhysicalValue (layerFraction θ) r k u.gradient q) =
      slabPhysicalValue (layerFraction θ) r k (regularMicroscopicResidualValue b F u ψ) q := by
  by_cases hq : coordinateRepresentative 1 q < layerFraction θ
  · have hfrac : (thetaRecovery b θ r k).value q =
        b.value (recoveryCoordinates (layerFraction θ) r k q) := by
      simp [thetaRecovery, recoveryFraction, hq]
    have hA : coefficientOperator (thetaRecovery b θ r k) q =
        coefficientOperator b (recoveryCoordinates (layerFraction θ) r k q) := by
      rw [coefficientOperator, hfrac]
      rfl
    simp only [slabPhysicalValue, ite_eq_left hq, hA]
    rfl
  · have hfrac : (thetaRecovery b θ r k).value q = pureFraction θ := by
      simp [thetaRecovery, recoveryFraction, hq]
    have hA : coefficientOperator (thetaRecovery b θ r k) q =
        Matrix.toEuclideanCLM (𝕜 := ℝ) (pureTensor θ) := by
      rw [coefficientOperator_eq_matrix, hfrac, pureTensor_eq_mixtureTensor]
    simp [slabPhysicalValue, hq, hA]

theorem idealResidual_eq_slab (b : PhaseFraction) (θ : ℝ)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (r k : ℕ) (F : PhysicalGradient)
    (u ψ : RegularPotential) :
    idealTrialFlux b θ hθ₀ hθ₁ r k F ψ - coefficientLaw (thetaRecovery b θ r k)
      (idealTrialField (layerFraction θ) r k F u) =
      slabMicroscopicResidual b θ r k F u ψ := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (idealTrialFlux b θ hθ₀ hθ₁ r k F ψ)
      (coefficientLaw (thetaRecovery b θ r k) (idealTrialField (layerFraction θ) r k F u)),
    Lp.coeFn_add (seedMacroFlux b θ hθ₀ hθ₁ F)
      (curlField (ψ.slabField (layerFraction θ) r k)),
    seedMacroFlux_coe b θ hθ₀ hθ₁ F,
    curlOperator.coeFn_compLpL (ψ.slabField (layerFraction θ) r k),
    ψ.slabField_coe (layerFraction θ) r k,
    coefficientLaw_coe (thetaRecovery b θ r k) (idealTrialField (layerFraction θ) r k F u),
    Lp.coeFn_add (constantField F) (u.slabField (layerFraction θ) r k),
    Lp.coeFn_const 2 domainMeasure F,
    u.slabField_coe (layerFraction θ) r k,
    slabPhysicalField_coe (layerFraction θ) r k (regularMicroscopicResidualValue b F u ψ)
      (regularMicroscopicResidualValue_measurable b F u ψ)
      (regularMicroscopicResidualBound b F u ψ) (regularMicroscopicResidualBound_nonneg b F u ψ)
      (regularMicroscopicResidualValue_bound b F u ψ)]
      with q hsub hadd hmacro hcurl hψ hA he hF hu hR
  change curlField (ψ.slabField (layerFraction θ) r k) q = _ at hcurl
  change constantField F q = _ at hF
  change slabMicroscopicResidual b θ r k F u ψ q = _ at hR
  change idealTrialFlux b θ hθ₀ hθ₁ r k F ψ q = _ at hadd
  change idealTrialField (layerFraction θ) r k F u q = _ at he
  rw [hsub]
  simp only [Pi.sub_apply, Pi.add_apply] at hadd he ⊢
  rw [hadd, hmacro, hcurl, hψ, hA, he, hF, hu, hR]
  exact idealResidualValue_eq b θ r k F u ψ q

theorem idealResidual_norm_le (b : PhaseFraction) (θ : ℝ)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) {r k : ℕ} (hr : 0 < r) (hk : 0 < k)
    (F : PhysicalGradient) (u ψ : RegularPotential) :
    ‖idealTrialFlux b θ hθ₀ hθ₁ r k F ψ - coefficientLaw (thetaRecovery b θ r k)
      (idealTrialField (layerFraction θ) r k F u)‖ ≤
      ‖regularMicroscopicResidual b F u ψ‖ := by
  rw [idealResidual_eq_slab]
  exact slabMicroscopicResidual_norm_le b hθ₀ hθ₁ hr hk F u ψ

end HierarchicalLaminates.Composition
