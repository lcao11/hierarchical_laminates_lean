module

public import HierarchicalLaminates.GClosure.TwoChildGeometry
public import HierarchicalLaminates.GClosure.GeneralLayerMacroFields

/-! Pointwise constitutive identities for two microscopic materials in an oblique layer. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open MeasureTheory Set HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material
  HierarchicalLaminates.Lamination HierarchicalLaminates.WeakCalculus HierarchicalLaminates.Binary
  HierarchicalLaminates.Homogenization HierarchicalLaminates.Composition

def firstChildLoading (R : TorusCoordinates) (b c : PhaseFraction) (a : ℝ)
    (F : PhysicalGradient) : PhysicalGradient :=
  firstPhysicalLayerField (effectiveMatrix b) (effectiveMatrix c) (coordinateNormal R) a F

def secondChildLoading (R : TorusCoordinates) (b c : PhaseFraction) (a : ℝ)
    (F : PhysicalGradient) : PhysicalGradient :=
  secondPhysicalLayerField (effectiveMatrix b) (effectiveMatrix c) (coordinateNormal R) a F

def twoChildMacroFieldValue (R : TorusCoordinates) (b c : PhaseFraction) (a : ℝ)
    (F : PhysicalGradient) (q : Domain) : PhysicalGradient :=
  if coordinateRepresentative 1 (R.equiv q) < a then firstChildLoading R b c a F
    else secondChildLoading R b c a F

def twoChildMacroFluxValue (R : TorusCoordinates) (b c : PhaseFraction) (a : ℝ)
    (F : PhysicalGradient) (q : Domain) : PhysicalGradient :=
  if coordinateRepresentative 1 (R.equiv q) < a then
    HierarchicalLaminates.Material.effectiveOperator b (firstChildLoading R b c a F)
    else HierarchicalLaminates.Material.effectiveOperator c (secondChildLoading R b c a F)

theorem twoChildMacroField_coe (R : TorusCoordinates) (b c : PhaseFraction)
    (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (F : PhysicalGradient) :
    generalLayerMacroField R a ha (effectiveMatrix b) (effectiveMatrix c) F =ᵐ[domainMeasure]
      twoChildMacroFieldValue R b c a F :=
  generalLayerMacroField_coe R a ha _ _ F

theorem twoChildMacroFlux_coe (R : TorusCoordinates) (b c : PhaseFraction)
    (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (F : PhysicalGradient) :
    generalLayerMacroFlux R a ha (effectiveMatrix b) (effectiveMatrix c) F =ᵐ[domainMeasure]
      twoChildMacroFluxValue R b c a F := by
  unfold twoChildMacroFluxValue firstChildLoading secondChildLoading
  simpa only [firstPhysicalLayerFlux,secondPhysicalLayerFlux,effectiveMatrix_operator] using
      generalLayerMacroFlux_coe R a ha (effectiveMatrix_posDef b) (effectiveMatrix_posDef c) F

def firstMicroValue (R : TorusCoordinates) (a : ℝ) (r k : ℕ)
    (f : Domain → PhysicalGradient) (q : Domain) : PhysicalGradient :=
  if coordinateRepresentative 1 (R.equiv q) < a then f (obliqueRecoveryCoordinates R a r k q)
    else 0

def secondMicroValue (R : TorusCoordinates) (a : ℝ) (r k : ℕ)
    (f : Domain → PhysicalGradient) (q : Domain) : PhysicalGradient :=
  if coordinateRepresentative 1 (R.equiv q) < a then 0
    else f (obliqueComplementCoordinates R a r k q)

theorem twoChildResidualValue_eq (R : TorusCoordinates) (b c : PhaseFraction) (a : ℝ)
    (r₁ k₁ r₂ k₂ : ℕ) (F : PhysicalGradient) (u₁ ψ₁ u₂ ψ₂ : RegularPotential)
    (q : Domain) :
    twoChildMacroFluxValue R b c a F q +
      curlOperator (firstMicroValue R a r₁ k₁ ψ₁.gradient q +
        secondMicroValue R a r₂ k₂ ψ₂.gradient q) -
      coefficientOperator (twoChildRecovery R b c a r₁ k₁ r₂ k₂) q
        (twoChildMacroFieldValue R b c a F q + firstMicroValue R a r₁ k₁ u₁.gradient q +
          secondMicroValue R a r₂ k₂ u₂.gradient q) =
      firstMicroValue R a r₁ k₁
        (regularMicroscopicResidualValue b (firstChildLoading R b c a F) u₁ ψ₁) q +
      secondMicroValue R a r₂ k₂
        (regularMicroscopicResidualValue c (secondChildLoading R b c a F) u₂ ψ₂) q := by
  by_cases hq : coordinateRepresentative 1 (R.equiv q) < a
  · have hA : coefficientOperator (twoChildRecovery R b c a r₁ k₁ r₂ k₂) q =
        coefficientOperator b (obliqueRecoveryCoordinates R a r₁ k₁ q) := by
      simp only [coefficientOperator,twoChildRecovery,ite_eq_left hq]
    simp only [twoChildMacroFluxValue,twoChildMacroFieldValue,firstMicroValue,secondMicroValue,
      ite_eq_left hq,add_zero,hA]
    rfl
  · have hA : coefficientOperator (twoChildRecovery R b c a r₁ k₁ r₂ k₂) q =
        coefficientOperator c (obliqueComplementCoordinates R a r₂ k₂ q) := by
      simp only [coefficientOperator,twoChildRecovery,ite_eq_right hq]
    simp only [twoChildMacroFluxValue,twoChildMacroFieldValue,firstMicroValue,secondMicroValue,
      ite_eq_right hq,zero_add,add_zero,hA]
    rfl

theorem physicalField_add_coe {e f : PhysicalField} {ev fv : Domain → PhysicalGradient}
    (he : e =ᵐ[domainMeasure] ev) (hf : f =ᵐ[domainMeasure] fv) :
    e + f =ᵐ[domainMeasure] fun q => ev q + fv q := by
  filter_upwards [Lp.coeFn_add e f,he,hf] with q hsum heq hfq
  simp only [Pi.add_apply] at hsum
  rw [hsum,heq,hfq]

theorem curlPhysicalField_coe {e : PhysicalField} {ev : Domain → PhysicalGradient}
    (he : e =ᵐ[domainMeasure] ev) :
    curlField e =ᵐ[domainMeasure] fun q => curlOperator (ev q) := by
  filter_upwards [curlOperator.coeFn_compLpL e,he] with q hcurl heq
  change curlField e q = _ at hcurl
  rw [hcurl,heq]

theorem residual_eq_of_ae (b : PhaseFraction) (e j r : PhysicalField)
    (ev jv rv : Domain → PhysicalGradient)
    (he : e =ᵐ[domainMeasure] ev) (hj : j =ᵐ[domainMeasure] jv)
    (hr : r =ᵐ[domainMeasure] rv)
    (hvalue : ∀ q, jv q - coefficientOperator b q (ev q) = rv q) :
    j - coefficientLaw b e = r := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub j (coefficientLaw b e),coefficientLaw_coe b e,he,hj,hr]
    with q hsub hA heq hjq hrq
  simp only [Pi.sub_apply] at hsub
  rw [hsub,hA,heq,hjq,hrq]
  exact hvalue q

end HierarchicalLaminates.GClosure
