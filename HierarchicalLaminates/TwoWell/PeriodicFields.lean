module

public import HierarchicalLaminates.TwoWell.Base
public import HierarchicalLaminates.Composition.FourierApproximation
public import HierarchicalLaminates.GClosure.DimensionSixteenBridge

/-! Rotation of periodic fields and density of stream gradients. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.TwoWell

open MeasureTheory HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.WeakCalculus
  HierarchicalLaminates.Analysis HierarchicalLaminates.Material HierarchicalLaminates.Composition

def rotatePhysical : PhysicalGradient →L[ℝ] PhysicalGradient := -curlOperator

def rotateField : PhysicalField →L[ℝ] PhysicalField := -curlField

theorem rotatePhysical_apply (v : PhysicalGradient) :
    (rotatePhysical v : Gradient16) = rotate (v : Gradient16) := by
  ext c
  rcases c with ⟨i,a⟩
  fin_cases i
  · simp [rotatePhysical,rotate,curlOperator_apply_zero]
  · simp [rotatePhysical,rotate,curlOperator_apply_one]

theorem rotateField_curl (g : PhysicalField) : rotateField (curlField g) = g := by
  apply HierarchicalLaminates.GClosure.physicalField_ext
  intro i a
  fin_cases i
  · simp [rotateField,curlField_component_zero,curlField_component_one]
  · simp [rotateField,curlField_component_zero,curlField_component_one]

theorem rotateField_eq_lift :
    rotateField = rotatePhysical.compLpL 2 domainMeasure := by
  apply ContinuousLinearMap.ext
  intro g
  apply Lp.ext
  filter_upwards [Lp.coeFn_neg (curlField g),curlOperator.coeFn_compLpL g,
    rotatePhysical.coeFn_compLpL g] with q hn hc hr
  change (-curlField g) q = _
  change curlField g q = curlOperator (g q) at hc
  simp only [Pi.neg_apply] at hn
  rw [hn,hc,hr]
  rfl

theorem rotateField_constant (F : PhysicalGradient) :
    rotateField (constantField F) = constantField (rotatePhysical F) := by
  rw [rotateField_eq_lift]
  apply Lp.ext
  filter_upwards [rotatePhysical.coeFn_compLpL (constantField F),
    Lp.coeFn_const 2 domainMeasure F,
    Lp.coeFn_const 2 domainMeasure (rotatePhysical F)] with q hr hF hout
  change constantField F q = F at hF
  change constantField (rotatePhysical F) q = rotatePhysical F at hout
  rw [hr,hF,hout]

theorem rotateField_mean (g : PhysicalField) :
    meanField (rotateField g) = rotatePhysical (meanField g) := by
  rw [rotateField_eq_lift,meanField_comp]

/-- A mean-zero equilibrium flux rotates into the closed space of periodic weak gradients. -/
theorem rotate_equilibrium_mem_gradientSpace (j : PhysicalField)
    (hm : meanField j = 0)
    (hj : ∀ g ∈ gradientSpace, inner ℝ j g = 0) :
    rotateField j ∈ gradientSpace := by
  have hsub : regularCurls ≤ gradientSpace.comap rotateField.toLinearMap := by
    rintro f ⟨_,⟨u,rfl⟩,rfl⟩
    change rotateField (curlField u.field) ∈ gradientSpace
    rw [rotateField_curl]
    exact u.mem_gradientSpace
  have hclosed : IsClosed (gradientSpace.comap rotateField.toLinearMap : Set PhysicalField) :=
    weakGradientSpace.isClosed_topologicalClosure.preimage rotateField.continuous
  exact regularCurls.topologicalClosure_minimal hsub hclosed
    (mem_regularCurls_closure j hm hj)

def exactCellField (b : PhaseFraction) (F : PhysicalGradient) : PhysicalField :=
  cellField gradientSpace (coefficientLaw b) (1/4) (by norm_num)
    (coefficientLaw_coercive b) (constantField F)

theorem exactCellField_isCell (b : PhaseFraction) (F : PhysicalGradient) :
    IsCellField gradientSpace (coefficientLaw b) (constantField F) (exactCellField b F) :=
  cellField_isCellField _ _ _ _ _ _

theorem exactCellFlux_mean (b : PhaseFraction) (F : PhysicalGradient) :
    meanField (coefficientLaw b (exactCellField b F)) =
      HierarchicalLaminates.Material.effectiveOperator b F := rfl

theorem exactCellField_energy (b : PhaseFraction) (F : PhysicalGradient) :
    inner ℝ (coefficientLaw b (exactCellField b F)) (exactCellField b F) =
      HierarchicalLaminates.Lamination.quadraticEnergy (effectiveMatrix b) (F : Gradient16) := by
  have h := effectiveOperator_energy gradientSpace constantField meanField
    constant_mean_pairing (coefficientLaw b) (1/4) (by norm_num)
      (coefficientLaw_coercive b) F
  change inner ℝ (HierarchicalLaminates.Material.effectiveOperator b F) F = _ at h
  rw [←effectiveMatrix_operator] at h
  rw [real_inner_comm,Matrix.inner_toEuclideanCLM] at h
  exact h.symm

theorem exactCellFlux_rotation_admissible (b : PhaseFraction) (F : PhysicalGradient) :
    rotateField (coefficientLaw b (exactCellField b F)) -
        constantField (rotatePhysical (HierarchicalLaminates.Material.effectiveOperator b F))
      ∈ gradientSpace := by
  let j := coefficientLaw b (exactCellField b F)
  have hm : meanField (j-constantField (meanField j)) = 0 := by
    rw [map_sub,mean_constantField,sub_self]
  have hj (g : PhysicalField) (hg : g ∈ gradientSpace) :
      inner ℝ (j-constantField (meanField j)) g = 0 := by
    rw [inner_sub_left,(exactCellField_isCell b F).2 g hg,
      constant_mean_pairing,gradientSpace_mean_zero g hg,inner_zero_right,sub_self]
  have h := rotate_equilibrium_mem_gradientSpace _ hm hj
  rw [map_sub,rotateField_constant,exactCellFlux_mean] at h
  exact h

end HierarchicalLaminates.TwoWell
