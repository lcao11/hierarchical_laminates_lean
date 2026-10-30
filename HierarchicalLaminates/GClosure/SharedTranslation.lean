module
public import HierarchicalLaminates.GClosure.Interfaces
public import Mathlib.MeasureTheory.Group.Measure
/-!
# Translation of periodic fields and complementary slabs
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace HierarchicalLaminates.GClosure
open MeasureTheory HierarchicalLaminates.Periodic HierarchicalLaminates.Binary HierarchicalLaminates.Homogenization HierarchicalLaminates.Composition
local instance : Measure.IsAddRightInvariant domainMeasure := by
  dsimp [domainMeasure]
  infer_instance
def shiftVertical (a : ℝ) (q : Domain) : Domain := coordinateFlow 1 q (-a)
theorem shiftVertical_continuous (a : ℝ) : Continuous (shiftVertical a) :=
  continuous_id.add continuous_const
theorem shiftVertical_measurable (a : ℝ) : Measurable (shiftVertical a) :=
  (shiftVertical_continuous a).measurable
theorem shiftVertical_measurePreserving (a : ℝ) :
    MeasurePreserving (shiftVertical a) domainMeasure domainMeasure :=
  measurePreserving_add_right domainMeasure (Pi.single 1 ((-a : ℝ) : UnitAddCircle))
theorem shiftVertical_inverse (a : ℝ) (q : Domain) :
    shiftVertical (-a) (shiftVertical a q) = q := by
  simp only [shiftVertical, coordinateFlow, neg_neg]
  ext i
  fin_cases i <;> simp
theorem shiftVertical_flow (a : ℝ) (i : Fin 2) (q : Domain) (s : ℝ) :
    shiftVertical a (coordinateFlow i q s) = coordinateFlow i (shiftVertical a q) s := by
  dsimp [shiftVertical, coordinateFlow]
  abel
def translateField {E : Type*} [NormedAddCommGroup E] (a : ℝ)
    (f : HierarchicalLaminates.Periodic.Field E) : HierarchicalLaminates.Periodic.Field E :=
  Lp.compMeasurePreserving (shiftVertical a) (shiftVertical_measurePreserving a) f
theorem translateField_coe {E : Type*} [NormedAddCommGroup E] (a : ℝ) (f : HierarchicalLaminates.Periodic.Field E) :
    translateField a f =ᵐ[domainMeasure] fun q => f (shiftVertical a q) :=
  Lp.coeFn_compMeasurePreserving f (shiftVertical_measurePreserving a)
theorem translateField_norm {E : Type*} [NormedAddCommGroup E] (a : ℝ) (f : HierarchicalLaminates.Periodic.Field E) :
    ‖translateField a f‖ = ‖f‖ := Lp.norm_compMeasurePreserving f _
theorem shiftVertical_integral (a : ℝ) (f : Domain → ℝ) (hf : Measurable f) :
    (∫ q, f (shiftVertical a q) ∂domainMeasure) = ∫ q, f q ∂domainMeasure := by
  have hp := shiftVertical_measurePreserving a
  have hfm : AEStronglyMeasurable f (Measure.map (shiftVertical a) domainMeasure) := by
    rw [hp.map_eq]
    exact hf.aestronglyMeasurable
  have h := integral_map hp.aemeasurable hfm
  rw [hp.map_eq] at h
  exact h.symm

theorem circleRepresentative_shift (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (q : Domain) :
    circleRepresentative (shiftVertical a q 1) =
      if a ≤ circleRepresentative (q 1) then circleRepresentative (q 1) - a
      else circleRepresentative (q 1) - a + 1 := by
  have hy := circleRepresentative_mem (q 1)
  have hy₀ := hy.1
  have hy₁ := hy.2
  have he : shiftVertical a q 1 = ((circleRepresentative (q 1) - a : ℝ) : UnitAddCircle) := by
    simp only [shiftVertical, coordinateFlow, Pi.add_apply, Pi.single_eq_same]
    rw [AddCircle.coe_sub, circleRepresentative_quotient]
    simp [sub_eq_add_neg]
  rw [he]
  split_ifs with h
  · exact circleRepresentative_coe ⟨by linarith, by linarith⟩
  · have hp : (((circleRepresentative (q 1) - a + 1 : ℝ) : UnitAddCircle)) =
        ((circleRepresentative (q 1) - a : ℝ) : UnitAddCircle) := AddCircle.coe_add_period _ _
    rw [← hp]
    exact circleRepresentative_coe ⟨by linarith, by linarith⟩

theorem shiftVertical_slab_iff {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1) (q : Domain) :
    coordinateRepresentative 1 (shiftVertical a q) < 1-a ↔ a ≤ coordinateRepresentative 1 q := by
  rw [coordinateRepresentative_eq_circleRepresentative, coordinateRepresentative_eq_circleRepresentative,
    circleRepresentative_shift a ha₀ ha₁]
  have hy := circleRepresentative_mem (q 1)
  have hy₀ := hy.1
  have hy₁ := hy.2
  split_ifs <;> constructor <;> intro h <;> linarith
def translatePotential (a : ℝ) (u : RegularPotential) : RegularPotential where
  potential c := (u.potential c).comp ⟨shiftVertical a, shiftVertical_continuous a⟩
  gradient := u.gradient.comp ⟨shiftVertical a, shiftVertical_continuous a⟩
  hasPartial i c q t := by
    change HasDerivAt (fun s => u.potential c (shiftVertical a (coordinateFlow i q s)))
      (u.gradient (shiftVertical a (coordinateFlow i q t)) (i,c)) t
    simpa only [shiftVertical_flow] using u.hasPartial i c (shiftVertical a q) t

theorem translatePotential_field (a : ℝ) (u : RegularPotential) :
    (translatePotential a u).field = translateField a u.field := by
  apply Lp.ext
  filter_upwards [translateField_coe a u.field,
    (shiftVertical_measurePreserving a).quasiMeasurePreserving.ae
      (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure u.gradient),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure
      (translatePotential a u).gradient] with q ht hu hs
  change u.field (shiftVertical a q) = u.gradient (shiftVertical a q) at hu
  change (translatePotential a u).field q = _ at hs
  rw [ht, hu, hs]
  rfl

theorem translatePotential_field_norm (a : ℝ) (u : RegularPotential) :
    ‖(translatePotential a u).field‖ = ‖u.field‖ := by
  rw [translatePotential_field, translateField_norm]
end HierarchicalLaminates.GClosure
