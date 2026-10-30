module

public import HierarchicalLaminates.Homogenization.ConventionalClosure
public import HierarchicalLaminates.Homogenization.FractionAlgebra
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Two-phase geometry for a horizontal recovery slab

The slab contains `r` complete horizontal periods and `k` complete vertical
periods of the inner coefficient. Integrating over these periods gives its
exact phase fraction.
-/

@[expose] public section
noncomputable section

namespace HierarchicalLaminates.Homogenization

open MeasureTheory HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material
open HierarchicalLaminates.Binary
open Set

local notation "μcircle" => AddCircle.haarAddCircle (T := (1 : ℝ))

def circleRepresentative (y : UnitAddCircle) : ℝ := (AddCircle.equivIco 1 0 y).1

theorem circleRepresentative_measurable : Measurable circleRepresentative :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable

theorem circleRepresentative_coe {y : ℝ} (hy : y ∈ Ico (0 : ℝ) 1) :
    circleRepresentative (y : UnitAddCircle) = y :=
  AddCircle.equivIco_coe_of_mem (by simpa using hy)

theorem circleIntegral_eq_Ico (f : UnitAddCircle → ℝ) :
    (∫ y, f y ∂μcircle) = ∫ y in Ico (0 : ℝ) 1, f (y : UnitAddCircle) := by
  have h := AddCircle.integral_preimage (1 : ℝ) 0 f
  rw [AddCircle.volume_eq_smul_haarAddCircle] at h
  simpa only [zero_add, ENNReal.ofReal_one, one_smul,
    integral_Ico_eq_integral_Ioc] using h.symm

theorem circleIntegral_eq_intervalIntegral (f : UnitAddCircle → ℝ) :
    (∫ y, f y ∂μcircle) = ∫ y in (0 : ℝ)..1, f (y : UnitAddCircle) := by
  rw [circleIntegral_eq_Ico, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ico_eq_integral_Ioc]

theorem circleCover_measurePreserving {r : ℕ} (hr : 0 < r) :
    MeasurePreserving (fun y : UnitAddCircle => r • y) μcircle μcircle := by
  have h := Measure.measurePreserving_zsmul μcircle
    (n := (r : ℤ)) (by exact_mod_cast (Nat.ne_of_gt hr))
  simpa only [natCast_zsmul] using h

theorem circleCover_integral {r : ℕ} (hr : 0 < r) {f : UnitAddCircle → ℝ}
    (hf : Measurable f) : (∫ y, f (r • y) ∂μcircle) = ∫ y, f y ∂μcircle := by
  have hp := circleCover_measurePreserving hr
  have hfm : AEStronglyMeasurable f (Measure.map (fun y : UnitAddCircle => r • y) μcircle) := by
    rw [hp.map_eq]
    exact hf.aestronglyMeasurable
  have hi := integral_map hp.aemeasurable hfm
  rw [hp.map_eq] at hi
  exact hi.symm

theorem stretchedCircle_integral {height : ℝ} (hh : 0 < height) {k : ℕ}
    (hk : 0 < k) {f : UnitAddCircle → ℝ} (hf : Measurable f) :
    (∫ y in Ico (0 : ℝ) height, f (k • (y / height : UnitAddCircle))) =
      height * ∫ z, f z ∂μcircle := by
  calc
    _ = ∫ y in (0 : ℝ)..height, f (k • (y / height : UnitAddCircle)) := by
      rw [intervalIntegral.integral_of_le hh.le, integral_Ico_eq_integral_Ioc]
    _ = height * ∫ y in (0 : ℝ)..1, f (k • (y : UnitAddCircle)) := by
      simpa only [zero_div, div_self hh.ne', smul_eq_mul] using
        intervalIntegral.integral_comp_div (a := 0) (b := height)
          (fun y : ℝ => f (k • (y : UnitAddCircle))) hh.ne'
    _ = height * ∫ z, f (k • z) ∂μcircle := by
      rw [← circleIntegral_eq_intervalIntegral (fun z => f (k • z))]
    _ = _ := by rw [circleCover_integral hk hf]

def verticalSlabValue (height : ℝ) (k : ℕ) (f : UnitAddCircle → ℝ) (i : ℝ)
    (y : UnitAddCircle) : ℝ :=
  if circleRepresentative y < height then f (k • (circleRepresentative y / height : UnitAddCircle))
    else i

theorem verticalSlab_integral {height : ℝ} (hh : height ∈ Ioc (0 : ℝ) 1)
    {k : ℕ} (hk : 0 < k) {f : UnitAddCircle → ℝ} (hf : Measurable f)
    (hfb : ∀ z, |f z| ≤ 1) (i : ℝ) (hi : |i| ≤ 1) :
    (∫ y, verticalSlabValue height k f i y ∂μcircle) =
      height * (∫ z, f z ∂μcircle) + (1 - height) * i := by
  let F : ℝ → ℝ := fun y => if y < height then f (k • (y / height : UnitAddCircle)) else i
  have hFm : Measurable F := Measurable.ite
    (measurableSet_lt measurable_id measurable_const)
    (hf.comp ((continuous_nsmul k).measurable.comp
      (AddCircle.measurable_mk'.comp (measurable_id.div_const height)))) measurable_const
  have hFb : ∀ y, ‖F y‖ ≤ 1 := by
    intro y
    simp only [F, Real.norm_eq_abs]
    split_ifs <;> first | exact hfb _ | exact hi
  have hint (a b : ℝ) : IntegrableOn F (Ico a b) :=
    IntegrableOn.of_bound (by simp [Real.volume_Ico]) hFm.aestronglyMeasurable.restrict 1
      (Filter.Eventually.of_forall hFb)
  rw [circleIntegral_eq_Ico]
  trans ∫ y in Ico (0 : ℝ) 1, F y
  · apply setIntegral_congr_fun measurableSet_Ico
    intro y hy
    simp only [verticalSlabValue, circleRepresentative_coe hy, F]
  rw [← Ico_union_Ico_eq_Ico hh.1.le hh.2,
    setIntegral_union Ico_disjoint_Ico_same measurableSet_Ico (hint 0 height) (hint height 1)]
  have hinside : (∫ y in Ico (0 : ℝ) height, F y) =
      ∫ y in Ico (0 : ℝ) height, f (k • (y / height : UnitAddCircle)) := by
    apply setIntegral_congr_fun measurableSet_Ico
    intro y hy
    simp only [F, ite_eq_left hy.2]
  have houtside : (∫ y in Ico height 1, F y) = (1 - height) * i := by
    calc
      _ = ∫ _y in Ico height 1, i := by
        apply setIntegral_congr_fun measurableSet_Ico
        intro y hy
        simp only [F, ite_eq_right (not_lt.mpr hy.1)]
      _ = _ := by simp [Measure.real, Real.volume_Ico, sub_nonneg.mpr hh.2]
  rw [hinside, houtside, stretchedCircle_integral hh.1 hk hf]

def recoveryCoordinates (height : ℝ) (r k : ℕ) (q : Domain) : Domain :=
  ![r • q 0, k • (coordinateRepresentative 1 q / height : UnitAddCircle)]

theorem recoveryCoordinates_measurable (height : ℝ) (r k : ℕ) :
    Measurable (recoveryCoordinates height r k) := by
  apply Measurable.of_eval
  intro i
  fin_cases i
  · exact (continuous_nsmul r).measurable.comp (measurable_pi_apply 0)
  · exact (continuous_nsmul k).measurable.comp
      (AddCircle.measurable_mk'.comp ((coordinateRepresentative_measurable 1).div_const height))

def recoveryFraction (b : PhaseFraction) (height : ℝ) (r k : ℕ) (i : ℝ)
    (hi : i ∈ Set.Icc (0 : ℝ) 1) : PhaseFraction where
  value q := if coordinateRepresentative 1 q < height then
    b.value (recoveryCoordinates height r k q) else i
  measurable := Measurable.ite
    (measurableSet_lt (coordinateRepresentative_measurable 1) measurable_const)
    (b.measurable.comp (recoveryCoordinates_measurable height r k)) measurable_const
  lower q := by split_ifs <;> first | exact b.lower _ | exact hi.1
  upper q := by split_ifs <;> first | exact b.upper _ | exact hi.2

theorem recoveryFraction_isBinary (b : PhaseFraction) (hb : IsBinary b)
    (height : ℝ) (r k : ℕ) (i : ℝ) (hi : i ∈ Set.Icc (0 : ℝ) 1)
    (hiBinary : i = 0 ∨ i = 1) : IsBinary (recoveryFraction b height r k i hi) := by
  intro q
  change (if coordinateRepresentative 1 q < height then _ else _) = 0 ∨
    (if coordinateRepresentative 1 q < height then _ else _) = 1
  split_ifs
  · exact hb _
  · exact hiBinary

theorem recoveryFraction_inside (b : PhaseFraction) (height : ℝ) (r k : ℕ) (i : ℝ)
    (hi : i ∈ Set.Icc (0 : ℝ) 1) {q : Domain}
    (hq : coordinateRepresentative 1 q < height) :
    (recoveryFraction b height r k i hi).value q = b.value (recoveryCoordinates height r k q) :=
  ite_eq_left hq

theorem recoveryFraction_outside (b : PhaseFraction) (height : ℝ) (r k : ℕ) (i : ℝ)
    (hi : i ∈ Set.Icc (0 : ℝ) 1) {q : Domain}
    (hq : height ≤ coordinateRepresentative 1 q) :
    (recoveryFraction b height r k i hi).value q = i :=
  ite_eq_right (not_lt.mpr hq)

theorem recoveryFraction_integrable (b : PhaseFraction) (height : ℝ) (r k : ℕ)
    (i : ℝ) (hi : i ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (recoveryFraction b height r k i hi).value domainMeasure := by
  apply Integrable.of_bound (recoveryFraction b height r k i hi).measurable.aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro q
  rw [Real.norm_eq_abs, abs_of_nonneg ((recoveryFraction b height r k i hi).lower q)]
  exact (recoveryFraction b height r k i hi).upper q

theorem phaseFraction_product_measurable (b : PhaseFraction) :
    Measurable (fun p : UnitAddCircle × UnitAddCircle => b.value ![p.1, p.2]) := by
  apply b.measurable.comp
  apply Measurable.of_eval
  intro i
  fin_cases i
  · exact measurable_fst
  · exact measurable_snd

theorem phaseFraction_abs_le (b : PhaseFraction) (q : Domain) : |b.value q| ≤ 1 := by
  rw [abs_of_nonneg (b.lower q)]
  exact b.upper q

theorem phaseMean_as_iterated (b : PhaseFraction) :
    phaseMean b = ∫ x : UnitAddCircle, ∫ y : UnitAddCircle, b.value ![x, y]
      ∂μcircle ∂μcircle := by
  have h := (measurePreserving_finTwoArrow μcircle).integral_comp'
    (fun p : UnitAddCircle × UnitAddCircle => b.value ![p.1, p.2])
  have hq : (fun q : Domain => b.value
      ![(MeasurableEquiv.finTwoArrow q).1, (MeasurableEquiv.finTwoArrow q).2]) = b.value := by
    funext q
    congr 1
    ext i
    fin_cases i <;> rfl
  rw [hq] at h
  change (∫ q, b.value q ∂domainMeasure) = _ at h
  rw [phaseMean, h]
  apply integral_prod
  exact Integrable.of_bound (phaseFraction_product_measurable b).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun p => by
      simpa only [Real.norm_eq_abs] using phaseFraction_abs_le b ![p.1, p.2])

def phaseHorizontalMean (b : PhaseFraction) (x : UnitAddCircle) : ℝ :=
  ∫ y : UnitAddCircle, b.value ![x, y] ∂μcircle

theorem phaseHorizontalMean_measurable (b : PhaseFraction) :
    Measurable (phaseHorizontalMean b) :=
  (phaseFraction_product_measurable b).stronglyMeasurable.integral_prod_right'.measurable

theorem phaseHorizontalMean_norm_le (b : PhaseFraction) (x : UnitAddCircle) :
    ‖phaseHorizontalMean b x‖ ≤ 1 := by
  have h := norm_integral_le_of_norm_le_const (μ := μcircle)
    (Filter.Eventually.of_forall fun y : UnitAddCircle =>
      show ‖b.value ![x, y]‖ ≤ 1 from by
        simpa only [Real.norm_eq_abs] using phaseFraction_abs_le b ![x, y])
  simpa only [phaseHorizontalMean, Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using h

/-- Exact constituent fraction of the recovery arrangement, including
irrational slab heights and every positive integer pair of microscopic periods. -/
theorem recoveryFraction_mean (b : PhaseFraction) {height : ℝ}
    (hh : height ∈ Ioc (0 : ℝ) 1) {r k : ℕ} (hr : 0 < r) (hk : 0 < k)
    (i : ℝ) (hi : i ∈ Icc (0 : ℝ) 1) :
    phaseMean (recoveryFraction b height r k i hi) =
      height * phaseMean b + (1 - height) * i := by
  rw [phaseMean_as_iterated]
  have hy (x : UnitAddCircle) :
      (∫ y : UnitAddCircle, (recoveryFraction b height r k i hi).value ![x, y] ∂μcircle) =
        height * phaseHorizontalMean b (r • x) + (1 - height) * i := by
    change (∫ y : UnitAddCircle,
      verticalSlabValue height k (fun z => b.value ![r • x, z]) i y ∂μcircle) = _
    apply verticalSlab_integral hh hk
    · apply b.measurable.comp
      apply Measurable.of_eval
      intro a
      fin_cases a
      · exact measurable_const
      · exact measurable_id
    · exact fun z => phaseFraction_abs_le b _
    · rw [abs_of_nonneg hi.1]
      exact hi.2
  simp_rw [hy]
  have hmean : Integrable (fun x : UnitAddCircle => phaseHorizontalMean b (r • x)) μcircle :=
    Integrable.of_bound
      ((phaseHorizontalMean_measurable b).comp (continuous_nsmul r).measurable).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => phaseHorizontalMean_norm_le b _)
  rw [integral_add (hmean.const_mul height) (integrable_const _), integral_const_mul,
    circleCover_integral hr (phaseHorizontalMean_measurable b)]
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  congr 1
  exact congrArg (fun t : ℝ => height * t) (phaseMean_as_iterated b).symm

theorem pureFraction_mem_forRecovery (θ : ℝ) : pureFraction θ ∈ Icc (0 : ℝ) 1 := by
  rcases pureFraction_values θ with h | h <;> simp [h]

def thetaRecovery (b : PhaseFraction) (θ : ℝ) (r k : ℕ) : PhaseFraction :=
  recoveryFraction b (layerFraction θ) r k (pureFraction θ) (pureFraction_mem_forRecovery θ)

theorem thetaRecovery_isBinary (b : PhaseFraction) (hb : IsBinary b)
    (θ : ℝ) (r k : ℕ) : IsBinary (thetaRecovery b θ r k) :=
  recoveryFraction_isBinary b hb _ _ _ _ _ (pureFraction_values θ)

theorem thetaRecovery_mean (b : PhaseFraction) (hb : phaseMean b = 1 / 2)
    {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) {r k : ℕ} (hr : 0 < r) (hk : 0 < k) :
    phaseMean (thetaRecovery b θ r k) = θ := by
  rw [thetaRecovery, recoveryFraction_mean b
    ⟨layerFraction_pos hθ₀ hθ₁, layerFraction_le_one θ⟩ hr hk, hb]
  exact prescribed_fraction_mul θ

end HierarchicalLaminates.Homogenization
