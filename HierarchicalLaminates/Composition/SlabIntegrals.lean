module

public import HierarchicalLaminates.Composition.Interfaces
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-! Exact integral transport through a slab filled with complete microscopic periods. -/

@[expose] public section
noncomputable section

namespace HierarchicalLaminates.Composition

open MeasureTheory Set HierarchicalLaminates.Homogenization HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Binary

local notation "μcircle" => AddCircle.haarAddCircle (T := (1 : ℝ))

theorem verticalSlab_integral_bounded {a : ℝ} (ha : a ∈ Ioc (0 : ℝ) 1)
    {k : ℕ} (hk : 0 < k) {f : UnitAddCircle → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ z, |f z| ≤ C) (i : ℝ) :
    (∫ y, verticalSlabValue a k f i y ∂μcircle) =
      a * (∫ z, f z ∂μcircle) + (1 - a) * i := by
  let F : ℝ → ℝ := fun y => if y < a then f (k • (y / a : UnitAddCircle)) else i
  have hFm : Measurable F := Measurable.ite
    (measurableSet_lt measurable_id measurable_const)
    (hf.comp ((continuous_nsmul k).measurable.comp
      (AddCircle.measurable_mk'.comp (measurable_id.div_const a)))) measurable_const
  have hFb : ∀ y, ‖F y‖ ≤ max C |i| := by
    intro y
    simp only [F, Real.norm_eq_abs]
    split_ifs
    · exact (hC _).trans (le_max_left _ _)
    · exact le_max_right _ _
  have hint (s t : ℝ) : IntegrableOn F (Ico s t) :=
    IntegrableOn.of_bound (by simp [Real.volume_Ico]) hFm.aestronglyMeasurable.restrict _
      (Filter.Eventually.of_forall hFb)
  rw [circleIntegral_eq_Ico]
  trans ∫ y in Ico (0 : ℝ) 1, F y
  · apply setIntegral_congr_fun measurableSet_Ico
    intro y hy
    simp only [verticalSlabValue, circleRepresentative_coe hy, F]
  rw [← Ico_union_Ico_eq_Ico ha.1.le ha.2,
    setIntegral_union Ico_disjoint_Ico_same measurableSet_Ico (hint 0 a) (hint a 1)]
  have hinside : (∫ y in Ico (0 : ℝ) a, F y) =
      ∫ y in Ico (0 : ℝ) a, f (k • (y / a : UnitAddCircle)) := by
    apply setIntegral_congr_fun measurableSet_Ico
    intro y hy
    simp only [F, ite_eq_left hy.2]
  have houtside : (∫ y in Ico a 1, F y) = (1 - a) * i := by
    calc
      _ = ∫ _y in Ico a 1, i := by
        apply setIntegral_congr_fun measurableSet_Ico
        intro y hy
        simp only [F, ite_eq_right (not_lt.mpr hy.1)]
      _ = _ := by simp [Measure.real, Real.volume_Ico, sub_nonneg.mpr ha.2]
  rw [hinside, houtside, stretchedCircle_integral ha.1 hk hf]

theorem bounded_integral_as_iterated (f : Domain → ℝ) (hf : Measurable f)
    {C : ℝ} (hC : ∀ q, |f q| ≤ C) :
    (∫ q, f q ∂domainMeasure) =
      ∫ x : UnitAddCircle, ∫ y : UnitAddCircle, f ![x,y] ∂μcircle ∂μcircle := by
  have hprod : Measurable (fun p : UnitAddCircle × UnitAddCircle => f ![p.1,p.2]) := by
    apply hf.comp
    apply Measurable.of_eval
    intro i
    fin_cases i
    · exact measurable_fst
    · exact measurable_snd
  have h := (measurePreserving_finTwoArrow μcircle).integral_comp'
    (fun p : UnitAddCircle × UnitAddCircle => f ![p.1,p.2])
  have hq : (fun q : Domain => f
      ![(MeasurableEquiv.finTwoArrow q).1, (MeasurableEquiv.finTwoArrow q).2]) = f := by
    funext q
    congr 1
    ext i
    fin_cases i <;> rfl
  rw [hq] at h
  change (∫ q, f q ∂domainMeasure) = _ at h
  rw [h]
  apply integral_prod
  exact Integrable.of_bound hprod.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hC ![p.1,p.2])

def slabValue (a : ℝ) (r k : ℕ) (f : Domain → ℝ) (q : Domain) : ℝ :=
  if coordinateRepresentative 1 q < a then f (recoveryCoordinates a r k q) else 0

theorem slabValue_measurable (a : ℝ) (r k : ℕ) (f : Domain → ℝ) (hf : Measurable f) :
    Measurable (slabValue a r k f) :=
  Measurable.ite (measurableSet_lt (coordinateRepresentative_measurable 1) measurable_const)
    (hf.comp (recoveryCoordinates_measurable a r k)) measurable_const

theorem slabValue_abs_le (a : ℝ) (r k : ℕ) (f : Domain → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ q, |f q| ≤ C) (q : Domain) :
    |slabValue a r k f q| ≤ C := by
  unfold slabValue
  split_ifs
  · exact hf _
  · simpa using hC

theorem slabValue_integral {a : ℝ} (ha : a ∈ Ioc (0 : ℝ) 1)
    {r k : ℕ} (hr : 0 < r) (hk : 0 < k) (f : Domain → ℝ) (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hfb : ∀ q, |f q| ≤ C) :
    (∫ q, slabValue a r k f q ∂domainMeasure) = a * ∫ q, f q ∂domainMeasure := by
  rw [bounded_integral_as_iterated _ (slabValue_measurable a r k f hf)
    (slabValue_abs_le a r k f hC hfb)]
  have hy (x : UnitAddCircle) :
      (∫ y : UnitAddCircle, slabValue a r k f ![x,y] ∂μcircle) =
        a * ∫ y : UnitAddCircle, f ![r • x,y] ∂μcircle := by
    change (∫ y : UnitAddCircle, verticalSlabValue a k (fun z => f ![r • x,z]) 0 y
      ∂μcircle) = _
    have hfm : Measurable (fun z : UnitAddCircle => f ![r • x,z]) := by
      apply hf.comp
      apply Measurable.of_eval
      intro i
      fin_cases i
      · exact measurable_const
      · exact measurable_id
    simpa using verticalSlab_integral_bounded ha hk hfm (C := C)
      (fun z => hfb ![r • x,z]) 0
  simp_rw [hy]
  rw [integral_const_mul]
  have hmean : Measurable (fun x : UnitAddCircle => ∫ y : UnitAddCircle, f ![x,y] ∂μcircle) := by
    have hp : Measurable (fun p : UnitAddCircle × UnitAddCircle => f ![p.1,p.2]) := by
      apply hf.comp
      apply Measurable.of_eval
      intro i
      fin_cases i
      · exact measurable_fst
      · exact measurable_snd
    exact hp.stronglyMeasurable.integral_prod_right'.measurable
  rw [circleCover_integral hr hmean, ← bounded_integral_as_iterated f hf hfb]

/-- A bounded measurable physical field and its pointwise representative. -/
def boundedPhysicalField (f : Domain → PhysicalGradient) (hf : Measurable f)
    (C : ℝ) (hC : ∀ q, ‖f q‖ ≤ C) : PhysicalField :=
  (MemLp.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hC)).toLp f

theorem boundedPhysicalField_coe (f : Domain → PhysicalGradient) (hf : Measurable f)
    (C : ℝ) (hC : ∀ q, ‖f q‖ ≤ C) :
    boundedPhysicalField f hf C hC =ᵐ[domainMeasure] f :=
  MemLp.coeFn_toLp _

theorem boundedPhysicalField_norm_sq (f : Domain → PhysicalGradient) (hf : Measurable f)
    (C : ℝ) (hC : ∀ q, ‖f q‖ ≤ C) :
    ‖boundedPhysicalField f hf C hC‖ ^ 2 = ∫ q, ‖f q‖ ^ 2 ∂domainMeasure := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [boundedPhysicalField_coe f hf C hC] with q hq
  rw [hq, real_inner_self_eq_norm_sq]

def slabPhysicalValue (a : ℝ) (r k : ℕ) (f : Domain → PhysicalGradient)
    (q : Domain) : PhysicalGradient :=
  if coordinateRepresentative 1 q < a then f (recoveryCoordinates a r k q) else 0

theorem slabPhysicalValue_measurable (a : ℝ) (r k : ℕ)
    (f : Domain → PhysicalGradient) (hf : Measurable f) :
    Measurable (slabPhysicalValue a r k f) :=
  Measurable.ite (measurableSet_lt (coordinateRepresentative_measurable 1) measurable_const)
    (hf.comp (recoveryCoordinates_measurable a r k)) measurable_const

theorem slabPhysicalValue_bound (a : ℝ) (r k : ℕ) (f : Domain → PhysicalGradient)
    {C : ℝ} (hC : 0 ≤ C) (hfb : ∀ q, ‖f q‖ ≤ C) (q : Domain) :
    ‖slabPhysicalValue a r k f q‖ ≤ C := by
  unfold slabPhysicalValue
  split_ifs
  · exact hfb _
  · simpa using hC

def slabPhysicalField (a : ℝ) (r k : ℕ) (f : Domain → PhysicalGradient)
    (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hfb : ∀ q, ‖f q‖ ≤ C) : PhysicalField :=
  boundedPhysicalField (slabPhysicalValue a r k f) (slabPhysicalValue_measurable a r k f hf)
    C (slabPhysicalValue_bound a r k f hC hfb)

theorem slabPhysicalField_coe (a : ℝ) (r k : ℕ) (f : Domain → PhysicalGradient)
    (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hfb : ∀ q, ‖f q‖ ≤ C) :
    slabPhysicalField a r k f hf C hC hfb =ᵐ[domainMeasure] slabPhysicalValue a r k f :=
  boundedPhysicalField_coe _ _ _ _

/-- Exact squared L² scaling for a bounded measurable residual. -/
theorem slabPhysicalField_norm_sq {a : ℝ} (ha : a ∈ Ioc (0 : ℝ) 1)
    {r k : ℕ} (hr : 0 < r) (hk : 0 < k) (f : Domain → PhysicalGradient)
    (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hfb : ∀ q, ‖f q‖ ≤ C) :
    ‖slabPhysicalField a r k f hf C hC hfb‖ ^ 2 =
      a * ‖boundedPhysicalField f hf C hfb‖ ^ 2 := by
  rw [slabPhysicalField, boundedPhysicalField_norm_sq, boundedPhysicalField_norm_sq]
  have heq : (fun q => ‖slabPhysicalValue a r k f q‖ ^ 2) =
      slabValue a r k (fun q => ‖f q‖ ^ 2) := by
    funext q
    unfold slabPhysicalValue slabValue
    split_ifs <;> simp
  rw [heq]
  apply slabValue_integral ha hr hk _ (hf.norm.pow_const 2) (sq_nonneg C)
  intro q
  rw [abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hfb q) 2

theorem slabPhysicalField_norm {a : ℝ} (ha : a ∈ Ioc (0 : ℝ) 1)
    {r k : ℕ} (hr : 0 < r) (hk : 0 < k) (f : Domain → PhysicalGradient)
    (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hfb : ∀ q, ‖f q‖ ≤ C) :
    ‖slabPhysicalField a r k f hf C hC hfb‖ =
      Real.sqrt a * ‖boundedPhysicalField f hf C hfb‖ := by
  have hs := slabPhysicalField_norm_sq ha hr hk f hf C hC hfb
  have hroot : (Real.sqrt a * ‖boundedPhysicalField f hf C hfb‖) ^ 2 =
      a * ‖boundedPhysicalField f hf C hfb‖ ^ 2 := by
    rw [mul_pow,Real.sq_sqrt ha.1.le]
  have hn := norm_nonneg (slabPhysicalField a r k f hf C hC hfb)
  have hnon := mul_nonneg (Real.sqrt_nonneg a) (norm_nonneg (boundedPhysicalField f hf C hfb))
  nlinarith [sq_nonneg (‖slabPhysicalField a r k f hf C hC hfb‖ -
    Real.sqrt a * ‖boundedPhysicalField f hf C hfb‖)]

theorem slabPhysicalField_norm_le {a : ℝ} (ha : a ∈ Ioc (0 : ℝ) 1)
    {r k : ℕ} (hr : 0 < r) (hk : 0 < k) (f : Domain → PhysicalGradient)
    (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hfb : ∀ q, ‖f q‖ ≤ C) :
    ‖slabPhysicalField a r k f hf C hC hfb‖ ≤ ‖boundedPhysicalField f hf C hfb‖ := by
  have hs := slabPhysicalField_norm_sq ha hr hk f hf C hC hfb
  have hm := mul_le_mul_of_nonneg_right ha.2 (sq_nonneg ‖boundedPhysicalField f hf C hfb‖)
  nlinarith [norm_nonneg (slabPhysicalField a r k f hf C hC hfb),
    norm_nonneg (boundedPhysicalField f hf C hfb)]

end HierarchicalLaminates.Composition
