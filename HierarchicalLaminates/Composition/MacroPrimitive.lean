module

public import HierarchicalLaminates.Composition.SlabIntegrals
public import HierarchicalLaminates.Binary.StripeWeakDerivative

/-!
# Weak derivatives of the periodic primitive of a horizontal slab
-/

@[expose] public section
noncomputable section

namespace HierarchicalLaminates.Composition

open MeasureTheory Set HierarchicalLaminates.Homogenization HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Binary
open HierarchicalLaminates.Fourier HierarchicalLaminates.WeakCalculus

local notation "μcircle" => AddCircle.haarAddCircle (T := (1 : ℝ))

local instance : Measure.IsAddRightInvariant domainMeasure := by
  dsimp [domainMeasure]
  infer_instance

def slabIndicator (a : ℝ) (q : Domain) : ℝ :=
  if coordinateRepresentative 1 q < a then 1 else 0

def slabPrimitiveValue (a : ℝ) (q : Domain) : ℝ :=
  stripePrimitive 1 (coordinateRepresentative 1 q) a

def slabDerivativeValue (a : ℝ) (q : Domain) : ℝ := slabIndicator a q - a

theorem slabIndicator_measurable (a : ℝ) : Measurable (slabIndicator a) :=
  Measurable.ite (measurableSet_lt (coordinateRepresentative_measurable 1) measurable_const)
    measurable_const measurable_const

theorem slabPrimitiveValue_measurable (a : ℝ) : Measurable (slabPrimitiveValue a) := by
  unfold slabPrimitiveValue stripePrimitive
  exact measurable_const.mul (((coordinateRepresentative_measurable 1).min measurable_const).sub
    ((coordinateRepresentative_measurable 1).mul measurable_const))

theorem slabDerivativeValue_measurable (a : ℝ) : Measurable (slabDerivativeValue a) :=
  (slabIndicator_measurable a).sub measurable_const

theorem slabPrimitiveValue_bound {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (q : Domain) :
    |slabPrimitiveValue a q| ≤ 1 / 4 := by
  exact primitive_abs_bound (by norm_num) ⟨(coordinateRepresentative_mem 1 q).1,
    (coordinateRepresentative_mem 1 q).2.le⟩ ha

theorem slabDerivativeValue_bound {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (q : Domain) :
    |slabDerivativeValue a q| ≤ 1 := by
  unfold slabDerivativeValue slabIndicator
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith [ha.1,ha.2]

theorem invariant_horizontal_test_integral_zero (f : Domain → ℝ) (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hfb : ∀ q, |f q| ≤ C)
    (hinv : ∀ q s, f (coordinateFlow 0 q s) = f q) (test : SmoothTest) :
    (∫ q, f q * test.derivative 0 q ∂domainMeasure) = 0 := by
  let F : ℝ → Domain → ℝ := fun s q => f (coordinateFlow 0 q s) *
    test.value (coordinateFlow 0 q s)
  let F' : ℝ → Domain → ℝ := fun s q => f q * test.derivative 0 (coordinateFlow 0 q s)
  have hmeas (s : ℝ) : Measurable (F s) :=
    (hf.mul test.value.continuous.measurable).comp
      (continuous_id.add continuous_const).measurable
  have hmeas' (s : ℝ) : Measurable (F' s) := hf.mul
    ((test.derivative 0).continuous.comp (continuous_id.add continuous_const)).measurable
  have hFint : Integrable (F 0) domainMeasure := by
    apply Integrable.of_bound (hmeas 0).aestronglyMeasurable (C * ‖test.value‖)
    apply Filter.Eventually.of_forall
    intro q
    simp only [F, coordinateFlow_zero, norm_mul, Real.norm_eq_abs]
    exact mul_le_mul (hfb q) (test.value.norm_coe_le_norm q) (abs_nonneg _) hC
  have hbound : ∀ q s, ‖F' s q‖ ≤ C * ‖test.derivative 0‖ := by
    intro q s
    simp only [F', norm_mul, Real.norm_eq_abs]
    exact mul_le_mul (hfb q) ((test.derivative 0).norm_coe_le_norm _) (abs_nonneg _) hC
  have hderiv (q : Domain) (t : ℝ) : HasDerivAt (fun s => F s q) (F' t q) t := by
    have hd := (smoothTest_hasDerivAt_flow test 0 q t).const_mul (f q)
    convert hd using 1
    · funext s
      simp only [F, hinv]
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (μ := domainMeasure)
    (bound := fun _ => C * ‖test.derivative 0‖) (s := Set.univ) (x₀ := (0 : ℝ))
    Filter.univ_mem (Filter.Eventually.of_forall fun s => (hmeas s).aestronglyMeasurable)
    hFint (hmeas' 0).aestronglyMeasurable
    (Filter.Eventually.of_forall fun q s _ => hbound q s) (integrable_const _)
    (Filter.Eventually.of_forall fun q s _ => hderiv q s)
  have htranslation : (fun s => ∫ q, F s q ∂domainMeasure) =
      fun _ : ℝ => ∫ q, f q * test.value q ∂domainMeasure := by
    funext s
    exact integral_add_right_eq_self (fun q => f q * test.value q)
      (Pi.single 0 (s : UnitAddCircle))
  have hz := hd.2
  rw [htranslation] at hz
  have heq := hz.unique (hasDerivAt_const (0 : ℝ) (∫ q, f q * test.value q ∂domainMeasure))
  simpa only [F', coordinateFlow_zero] using heq

theorem slabPrimitiveValue_horizontal_test_zero {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (test : SmoothTest) :
    (∫ q, slabPrimitiveValue a q * test.derivative 0 q ∂domainMeasure) = 0 := by
  apply invariant_horizontal_test_integral_zero _ (slabPrimitiveValue_measurable a)
    (by norm_num : (0 : ℝ) ≤ 1/4) (slabPrimitiveValue_bound ha) _ test
  intro q s
  simp [slabPrimitiveValue,coordinateRepresentative,coordinateFlow]

theorem representative_vertical {y : ℝ} (hy : y ∈ Ico (0 : ℝ) 1)
    (x : UnitAddCircle) : coordinateRepresentative 1 ![x,(y : UnitAddCircle)] = y := by
  exact circleRepresentative_coe hy

theorem slabPrimitiveValue_vertical_test {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (test : SmoothTest) :
    (∫ q, slabPrimitiveValue a q * test.derivative 1 q ∂domainMeasure) =
      -(∫ q, slabDerivativeValue a q * test.value q ∂domainMeasure) := by
  have hpb (q : Domain) : |slabPrimitiveValue a q * test.derivative 1 q| ≤
      (1/4) * ‖test.derivative 1‖ := by
    rw [abs_mul]
    exact mul_le_mul (slabPrimitiveValue_bound ha q) ((test.derivative 1).norm_coe_le_norm q)
      (abs_nonneg _) (by norm_num)
  have hdb (q : Domain) : |slabDerivativeValue a q * test.value q| ≤ ‖test.value‖ := by
    rw [abs_mul]
    simpa using mul_le_mul (slabDerivativeValue_bound ha q) (test.value.norm_coe_le_norm q)
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  rw [bounded_integral_as_iterated (fun q => slabPrimitiveValue a q * test.derivative 1 q)
    ((slabPrimitiveValue_measurable a).mul (test.derivative 1).continuous.measurable) hpb,
    bounded_integral_as_iterated (fun q => slabDerivativeValue a q * test.value q)
    ((slabDerivativeValue_measurable a).mul test.value.continuous.measurable) hdb, ← integral_neg]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [circleIntegral_eq_intervalIntegral, circleIntegral_eq_intervalIntegral]
  have hp : (∫ y in (0 : ℝ)..1, slabPrimitiveValue a ![x,(y : UnitAddCircle)] *
      test.derivative 1 ![x,(y : UnitAddCircle)]) =
      ∫ y in (0 : ℝ)..1, stripePrimitive 1 y a * test.derivative 1 ![x,(y : UnitAddCircle)] := by
    apply integral_local_congr
    intro y hy
    rw [slabPrimitiveValue, representative_vertical hy]
  have hd : (∫ y in (0 : ℝ)..1, slabDerivativeValue a ![x,(y : UnitAddCircle)] *
      test.value ![x,(y : UnitAddCircle)]) =
      ∫ y in (0 : ℝ)..1, (stripeIndicator y a - a) * test.value ![x,(y : UnitAddCircle)] := by
    apply integral_local_congr
    intro y hy
    simp only [slabDerivativeValue,slabIndicator,representative_vertical hy,stripeIndicator]
  rw [hp,hd]
  have hab := smoothTest_pointInStrip_absolutelyContinuous test 1 0 x
  have hder := smoothTest_hasDerivAt_pointInStrip test 1 0 x
  simp only [pointInStrip, Nat.cast_one, Nat.cast_zero, zero_add, div_one,
    one_mul] at hab hder
  simpa only [one_mul] using stripePrimitive_integrationByParts (h := 1) ha hab hder

theorem slabPrimitiveValue_memLp {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    MemLp (slabPrimitiveValue a) 2 domainMeasure :=
  MemLp.of_bound (slabPrimitiveValue_measurable a).aestronglyMeasurable (1/4)
    (Filter.Eventually.of_forall fun q => by
      simpa only [Real.norm_eq_abs] using (slabPrimitiveValue_bound ha q))

theorem slabDerivativeValue_memLp {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    MemLp (slabDerivativeValue a) 2 domainMeasure :=
  MemLp.of_bound (slabDerivativeValue_measurable a).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun q => by
      simpa only [Real.norm_eq_abs] using (slabDerivativeValue_bound ha q))

def slabPrimitiveField (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) : ScalarField :=
  (slabPrimitiveValue_memLp ha).toLp (slabPrimitiveValue a)

def slabDerivativeField (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) : ScalarField :=
  (slabDerivativeValue_memLp ha).toLp (slabDerivativeValue a)

theorem toLp_inner_continuous (f : Domain → ℝ) (hf : MemLp f 2 domainMeasure)
    (t : C(Domain,ℝ)) :
    inner ℝ (hf.toLp f) (continuousField t) = ∫ q, f q * t q ∂domainMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hf,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure t] with q hq ht
  change inner ℝ (hf.toLp f q) (ContinuousMap.toLp 2 domainMeasure ℝ t q) = _
  rw [hq,ht]
  simp only [Real.inner_apply]

theorem slabPrimitiveField_horizontal {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    HasWeakPartial (slabPrimitiveField a ha) 0 0 := by
  intro test
  rw [inner_zero_left]
  change 0 = -inner ℝ ((slabPrimitiveValue_memLp ha).toLp (slabPrimitiveValue a)) _
  rw [toLp_inner_continuous, slabPrimitiveValue_horizontal_test_zero ha test, neg_zero]

theorem slabPrimitiveField_vertical {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    HasWeakPartial (slabPrimitiveField a ha) (slabDerivativeField a ha) 1 := by
  intro test
  change inner ℝ ((slabDerivativeValue_memLp ha).toLp (slabDerivativeValue a)) _ =
    -inner ℝ ((slabPrimitiveValue_memLp ha).toLp (slabPrimitiveValue a)) _
  rw [toLp_inner_continuous,toLp_inner_continuous,
    slabPrimitiveValue_vertical_test ha test,neg_neg]

end HierarchicalLaminates.Composition
