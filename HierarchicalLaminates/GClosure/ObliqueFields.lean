module

public import HierarchicalLaminates.GClosure.ObliquePullback

/-! Closed weak gradients and equilibrium under periodic coordinate changes. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open MeasureTheory HierarchicalLaminates.Periodic HierarchicalLaminates.WeakCalculus HierarchicalLaminates.Composition

def TorusCoordinates.symm (R : TorusCoordinates) : TorusCoordinates where
  matrix := R.inverse
  inverse := R.matrix
  inverse_mul := R.mul_inverse
  mul_inverse := R.inverse_mul

def TorusCoordinates.gradientPullback (R : TorusCoordinates) : PhysicalField →L[ℝ] PhysicalField :=
  ((spatialGradientMap R.matrix).compLpL 2 domainMeasure).comp
    R.pullbackField.toContinuousLinearMap

theorem TorusCoordinates.gradientPullback_norm_le (R : TorusCoordinates) (f : PhysicalField) :
    ‖R.gradientPullback f‖ ≤ ‖spatialGradientMap R.matrix‖ * ‖f‖ := by
  change ‖(spatialGradientMap R.matrix).compLp (R.pullbackField f)‖ ≤ _
  simpa only [R.pullbackField_norm] using
    (spatialGradientMap R.matrix).norm_compLp_le (R.pullbackField f)

theorem TorusCoordinates.gradientPullback_coe (R : TorusCoordinates) (f : PhysicalField) :
    R.gradientPullback f =ᵐ[domainMeasure] fun q =>
      spatialGradientMap R.matrix (f (R.equiv q)) := by
  filter_upwards [(spatialGradientMap R.matrix).coeFn_compLpL (R.pullbackField f),
    R.pullbackField_coe f] with q hmap hp
  change (spatialGradientMap R.matrix).compLpL 2 domainMeasure (R.pullbackField f) q = _
  rw [hmap,hp]

theorem TorusCoordinates.gradientPullback_regular (R : TorusCoordinates) (u : RegularPotential) :
    R.gradientPullback u.field = (transformPotential R.matrix u).field := by
  apply Lp.ext
  filter_upwards [R.gradientPullback_coe u.field,
    R.measurePreserving.quasiMeasurePreserving.ae
      (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure u.gradient),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure
      (transformPotential R.matrix u).gradient] with q hp hu ht
  change u.field (R.equiv q) = u.gradient (R.equiv q) at hu
  change (transformPotential R.matrix u).field q = _ at ht
  rw [hp,hu,ht]
  rfl

theorem TorusCoordinates.gradientPullback_mem (R : TorusCoordinates) (g : PhysicalField)
    (hg : g ∈ gradientSpace) : R.gradientPullback g ∈ gradientSpace := by
  let S := gradientSpace.comap R.gradientPullback.toLinearMap
  have hclosed : IsClosed (S : Set PhysicalField) :=
    weakGradientSpace.isClosed_topologicalClosure.preimage R.gradientPullback.continuous
  have hsub : regularGradients ≤ S := by
    rintro _ ⟨u,rfl⟩
    change R.gradientPullback u.field ∈ gradientSpace
    rw [R.gradientPullback_regular]
    exact (transformPotential R.matrix u).mem_gradientSpace
  have hmem : g ∈ regularGradients.topologicalClosure := by
    rw [regularGradients_closure_eq]
    exact hg
  exact regularGradients.topologicalClosure_minimal hsub hclosed hmem

theorem curlField_gradientSpace_orthogonal (g : PhysicalField) (hg : g ∈ gradientSpace)
    (h : PhysicalField) (hh : h ∈ gradientSpace) : inner ℝ (curlField g) h = 0 := by
  let L : PhysicalField →L[ℝ] ℝ := (innerSL ℝ h).comp curlField
  have hsub : weakGradientSpace ≤ L.ker := by
    rintro v ⟨u,hu⟩
    change inner ℝ h (curlField v) = 0
    rw [real_inner_comm]
    exact weakCurl_gradient_zero hu h hh
  have hm := weakGradientSpace.topologicalClosure_minimal hsub L.isClosed_ker hg
  change inner ℝ h (curlField g) = 0 at hm
  rwa [real_inner_comm] at hm

theorem curlField_gradientSpace_mean_zero (g : PhysicalField) (hg : g ∈ gradientSpace) :
    meanField (curlField g) = 0 := by
  rw [show curlField g = curlOperator.compLpL 2 domainMeasure g from rfl,
    meanField_comp, gradientSpace_mean_zero g hg, map_zero]

theorem TorusCoordinates.pullbackField_mean (R : TorusCoordinates) (f : PhysicalField) :
    meanField (R.pullbackField f) = meanField f := by
  rw [meanField_eq_integral,meanField_eq_integral]
  trans ∫ q, f (R.equiv q) ∂domainMeasure
  · exact integral_congr_ae (R.pullbackField_coe f)
  · have hp := R.measurePreserving
    have hfm : AEStronglyMeasurable f (Measure.map R.equiv domainMeasure) := by
      rw [hp.map_eq]
      exact Lp.aestronglyMeasurable f
    have h := integral_map hp.aemeasurable hfm
    rw [hp.map_eq] at h
    exact h.symm

end HierarchicalLaminates.GClosure
