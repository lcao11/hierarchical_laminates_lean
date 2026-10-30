module

public import HierarchicalLaminates.GClosure.ObliqueRecovery

/-! Exact norm transport for bounded residuals in periodic oblique slabs. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open MeasureTheory Set HierarchicalLaminates.Periodic HierarchicalLaminates.Composition

theorem TorusCoordinates.pullback_boundedPhysicalField (R : TorusCoordinates)
    (f : Domain → PhysicalGradient) (hf : Measurable f) (C : ℝ)
    (hb : ∀ q, ‖f q‖ ≤ C) :
    R.pullbackField (boundedPhysicalField f hf C hb) =
      boundedPhysicalField (fun q => f (R.equiv q))
        (hf.comp R.continuous.measurable) C (fun q => hb (R.equiv q)) := by
  apply Lp.ext
  filter_upwards [R.pullbackField_coe (boundedPhysicalField f hf C hb),
    R.measurePreserving.quasiMeasurePreserving.ae (boundedPhysicalField_coe f hf C hb),
    boundedPhysicalField_coe (fun q => f (R.equiv q))
      (hf.comp R.continuous.measurable) C (fun q => hb (R.equiv q))] with q hp hfq ho
  rw [hp,hfq,ho]

def obliqueSlabPhysicalField (R : TorusCoordinates) (a : ℝ) (r k : ℕ)
    (f : Domain → PhysicalGradient) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ q, ‖f q‖ ≤ C) : PhysicalField :=
  R.pullbackField (slabPhysicalField a r k (fun q => f (R.symm.equiv q))
    (hf.comp R.symm.continuous.measurable) C hC (fun q => hb (R.symm.equiv q)))

theorem obliqueSlabPhysicalField_coe (R : TorusCoordinates) (a : ℝ) (r k : ℕ)
    (f : Domain → PhysicalGradient) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ q, ‖f q‖ ≤ C) :
    obliqueSlabPhysicalField R a r k f hf C hC hb =ᵐ[domainMeasure] fun q =>
      if HierarchicalLaminates.Binary.coordinateRepresentative 1 (R.equiv q) < a then
        f (obliqueRecoveryCoordinates R a r k q) else 0 := by
  filter_upwards [R.pullbackField_coe
      (slabPhysicalField a r k (fun q => f (R.symm.equiv q))
        (hf.comp R.symm.continuous.measurable) C hC (fun q => hb (R.symm.equiv q))),
    R.measurePreserving.quasiMeasurePreserving.ae
      (slabPhysicalField_coe a r k (fun q => f (R.symm.equiv q))
        (hf.comp R.symm.continuous.measurable) C hC (fun q => hb (R.symm.equiv q)))] with q hp hs
  change R.pullbackField (slabPhysicalField a r k (fun q => f (R.symm.equiv q))
    (hf.comp R.symm.continuous.measurable) C hC (fun q => hb (R.symm.equiv q))) q = _
  rw [hp,hs]
  unfold slabPhysicalValue
  split_ifs <;> rfl

theorem obliqueSlabPhysicalField_norm_le (R : TorusCoordinates) {a : ℝ}
    (ha : a ∈ Ioc (0 : ℝ) 1) {r k : ℕ} (hr : 0 < r) (hk : 0 < k)
    (f : Domain → PhysicalGradient) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ q, ‖f q‖ ≤ C) :
    ‖obliqueSlabPhysicalField R a r k f hf C hC hb‖ ≤ ‖boundedPhysicalField f hf C hb‖ := by
  unfold obliqueSlabPhysicalField
  rw [R.pullbackField_norm]
  have h := slabPhysicalField_norm_le ha hr hk (fun q => f (R.symm.equiv q))
    (hf.comp R.symm.continuous.measurable) C hC (fun q => hb (R.symm.equiv q))
  rw [← R.symm.pullback_boundedPhysicalField,R.symm.pullbackField_norm] at h
  exact h

end HierarchicalLaminates.GClosure
