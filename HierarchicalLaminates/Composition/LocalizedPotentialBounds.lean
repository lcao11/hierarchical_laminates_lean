module

public import HierarchicalLaminates.Composition.LocalizedPotential
public import HierarchicalLaminates.Composition.IdealResidual
public import HierarchicalLaminates.WeakCalculus.Bounds

/-! Quantitative errors of localized gradients. -/

@[expose] public section
noncomputable section

namespace HierarchicalLaminates.Composition

open MeasureTheory HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Binary
  HierarchicalLaminates.WeakCalculus HierarchicalLaminates.Homogenization
open Set Filter
open scoped Topology

def cutoffDerivativeOnUnit (a δ : ℝ) : C(Icc (0 : ℝ) 1, ℝ) :=
  ⟨fun y => rawSlabCutoffDerivative a δ y,
    (rawSlabCutoffDerivative_continuous a δ).comp continuous_subtype_val⟩

def cutoffDerivativeBound (a δ : ℝ) : ℝ := ‖cutoffDerivativeOnUnit a δ‖

theorem cutoffDerivativeBound_nonneg (a δ : ℝ) : 0 ≤ cutoffDerivativeBound a δ := norm_nonneg _

theorem cutoffDerivative_abs_le (a δ : ℝ) (q : Domain) :
    |rawSlabCutoffDerivative a δ (coordinateRepresentative 1 q)| ≤ cutoffDerivativeBound a δ := by
  exact (cutoffDerivativeOnUnit a δ).norm_coe_le_norm
    ⟨coordinateRepresentative 1 q, (coordinateRepresentative_mem 1 q).1,
      (coordinateRepresentative_mem 1 q).2.le⟩

def potentialBound (u : RegularPotential) : ℝ := ∑ c : Fin 16, ‖u.potential c‖

theorem potentialBound_nonneg (u : RegularPotential) : 0 ≤ potentialBound u :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem potential_abs_le (u : RegularPotential) (c : Fin 16) (q : Domain) :
    |u.potential c q| ≤ potentialBound u := by
  exact ((u.potential c).norm_coe_le_norm q).trans
    (Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ c))

theorem regularGradient_component_abs_le (u : RegularPotential) (i : Fin 2) (c : Fin 16)
    (q : Domain) : |u.gradient q (i,c)| ≤ ‖u.gradient‖ := by
  exact (PiLp.norm_apply_le (u.gradient q) (i,c)).trans (u.gradient.norm_coe_le_norm q)

def boundedScalarField (f : Domain → ℝ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ q, |f q| ≤ C) : ScalarField :=
  (MemLp.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun q => by simpa only [Real.norm_eq_abs] using hC q)).toLp f

theorem boundedScalarField_coe (f : Domain → ℝ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ q, |f q| ≤ C) : boundedScalarField f hf C hC =ᵐ[domainMeasure] f :=
  MemLp.coeFn_toLp _

theorem boundedScalarField_norm_le (f : Domain → ℝ) (hf : Measurable f) (C : ℝ)
    (hC₀ : 0 ≤ C) (hC : ∀ q, |f q| ≤ C) : ‖boundedScalarField f hf C hC‖ ≤ C := by
  apply scalarField_norm_le_of_ae_bound _ hC₀
  filter_upwards [boundedScalarField_coe f hf C hC] with q hq
  rw [hq]
  exact hC q

def cutoffMismatchValue (a δ : ℝ) (r k : ℕ) (u : RegularPotential)
    (i : Fin 2) (c : Fin 16) (q : Domain) : ℝ :=
  (rawSlabCutoff a δ (coordinateRepresentative 1 q) - 1) *
    slabValue a r k (fun p => u.gradient p (i,c)) q

theorem cutoffMismatchValue_measurable (a δ : ℝ) (r k : ℕ) (u : RegularPotential)
    (i : Fin 2) (c : Fin 16) : Measurable (cutoffMismatchValue a δ r k u i c) :=
  (((rawSlabCutoff_contDiff a δ).continuous.measurable.comp
    (coordinateRepresentative_measurable 1)).sub measurable_const).mul
    (slabValue_measurable a r k _
      ((EuclideanSpace.proj (𝕜 := ℝ) (i,c)).continuous.measurable.comp u.gradient.continuous.measurable))

theorem cutoffMismatchValue_bound (a δ : ℝ) (r k : ℕ) (u : RegularPotential)
    (i : Fin 2) (c : Fin 16) (q : Domain) :
    |cutoffMismatchValue a δ r k u i c q| ≤ ‖u.gradient‖ := by
  have hη : |rawSlabCutoff a δ (coordinateRepresentative 1 q) - 1| ≤ 1 :=
    abs_le.mpr ⟨by linarith [rawSlabCutoff_nonneg a δ (coordinateRepresentative 1 q)],
      by linarith [rawSlabCutoff_le_one a δ (coordinateRepresentative 1 q)]⟩
  have hs := slabValue_abs_le a r k (fun p => u.gradient p (i,c)) (norm_nonneg u.gradient)
    (regularGradient_component_abs_le u i c) q
  unfold cutoffMismatchValue
  rw [abs_mul]
  exact (mul_le_mul hη hs (abs_nonneg _) (by norm_num)).trans (by simp)

def cutoffMismatchField (a δ : ℝ) (r k : ℕ) (u : RegularPotential)
    (i : Fin 2) (c : Fin 16) : ScalarField :=
  boundedScalarField (cutoffMismatchValue a δ r k u i c)
    (cutoffMismatchValue_measurable a δ r k u i c) ‖u.gradient‖
    (cutoffMismatchValue_bound a δ r k u i c)

def aspectErrorValue (a δ : ℝ) (r k : ℕ) (u : RegularPotential)
    (i : Fin 2) (c : Fin 16) (q : Domain) : ℝ :=
  if i = 0 then 0 else
    ((k : ℝ) / (a * r) - 1) * rawSlabCutoff a δ (coordinateRepresentative 1 q) *
      slabValue a r k (fun p => u.gradient p (1,c)) q

theorem aspectErrorValue_measurable (a δ : ℝ) (r k : ℕ) (u : RegularPotential)
    (i : Fin 2) (c : Fin 16) : Measurable (aspectErrorValue a δ r k u i c) := by
  unfold aspectErrorValue
  split_ifs
  · exact measurable_const
  · exact (measurable_const.mul ((rawSlabCutoff_contDiff a δ).continuous.measurable.comp
      (coordinateRepresentative_measurable 1))).mul
      (slabValue_measurable a r k _
        ((EuclideanSpace.proj (𝕜 := ℝ) (1,c)).continuous.measurable.comp u.gradient.continuous.measurable))

theorem aspectErrorValue_bound (a δ : ℝ) (r k : ℕ) (u : RegularPotential)
    (i : Fin 2) (c : Fin 16) (q : Domain) :
    |aspectErrorValue a δ r k u i c q| ≤ |(k : ℝ) / (a * r) - 1| * ‖u.gradient‖ := by
  unfold aspectErrorValue
  split_ifs
  · simp only [abs_zero]
    positivity
  · rw [abs_mul, abs_mul, abs_of_nonneg (rawSlabCutoff_nonneg _ _ _)]
    have hs := slabValue_abs_le a r k (fun p => u.gradient p (1,c)) (norm_nonneg u.gradient)
      (regularGradient_component_abs_le u 1 c) q
    calc
      _ ≤ |(k : ℝ) / (a * r) - 1| * 1 * ‖u.gradient‖ :=
        mul_le_mul (mul_le_mul_of_nonneg_left (rawSlabCutoff_le_one _ _ _) (abs_nonneg _))
          hs (abs_nonneg _) (by positivity)
      _ = _ := by ring

def aspectErrorField (a δ : ℝ) (r k : ℕ) (u : RegularPotential)
    (i : Fin 2) (c : Fin 16) : ScalarField :=
  boundedScalarField (aspectErrorValue a δ r k u i c)
    (aspectErrorValue_measurable a δ r k u i c) (|(k : ℝ) / (a * r) - 1| * ‖u.gradient‖)
    (aspectErrorValue_bound a δ r k u i c)

def derivativeErrorValue (a δ : ℝ) (r k : ℕ) (u : RegularPotential)
    (i : Fin 2) (c : Fin 16) (q : Domain) : ℝ :=
  if i = 0 then 0 else (r : ℝ)⁻¹ * rawSlabCutoffDerivative a δ (coordinateRepresentative 1 q) *
    u.potential c (recoveryCoordinates a r k q)

theorem derivativeErrorValue_measurable (a δ : ℝ) (r k : ℕ) (u : RegularPotential)
    (i : Fin 2) (c : Fin 16) : Measurable (derivativeErrorValue a δ r k u i c) := by
  unfold derivativeErrorValue
  split_ifs
  · exact measurable_const
  · exact (measurable_const.mul ((rawSlabCutoffDerivative_continuous a δ).measurable.comp
      (coordinateRepresentative_measurable 1))).mul
      ((u.potential c).continuous.measurable.comp (recoveryCoordinates_measurable a r k))

theorem derivativeErrorValue_bound (a δ : ℝ) (r k : ℕ) (u : RegularPotential)
    (i : Fin 2) (c : Fin 16) (q : Domain) :
    |derivativeErrorValue a δ r k u i c q| ≤
      (r : ℝ)⁻¹ * cutoffDerivativeBound a δ * potentialBound u := by
  unfold derivativeErrorValue
  split_ifs
  · simp only [abs_zero]
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg r))
      (cutoffDerivativeBound_nonneg a δ)) (potentialBound_nonneg u)
  · rw [abs_mul, abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg r))]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (cutoffDerivative_abs_le a δ q) (inv_nonneg.mpr (Nat.cast_nonneg r)))
      (potential_abs_le u c _) (abs_nonneg _)
      (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg r)) (cutoffDerivativeBound_nonneg a δ))

def derivativeErrorField (a δ : ℝ) (r k : ℕ) (u : RegularPotential)
    (i : Fin 2) (c : Fin 16) : ScalarField :=
  boundedScalarField (derivativeErrorValue a δ r k u i c)
    (derivativeErrorValue_measurable a δ r k u i c)
    ((r : ℝ)⁻¹ * cutoffDerivativeBound a δ * potentialBound u)
    (derivativeErrorValue_bound a δ r k u i c)

theorem localizedPotential_component_error_value {a δ : ℝ} (ha : a ≤ 1) (hδ : 0 < δ)
    (r k : ℕ) (u : RegularPotential) (i : Fin 2) (c : Fin 16) (q : Domain) :
    localizedPotentialGradient a δ ha hδ r k u q (i,c) -
        slabPhysicalValue a r k u.gradient q (i,c) =
      cutoffMismatchValue a δ r k u i c q + aspectErrorValue a δ r k u i c q +
        derivativeErrorValue a δ r k u i c q := by
  have hmap := microSlabCoordinates_eq_recoveryCoordinates a r k q
  by_cases hq : coordinateRepresentative 1 q < a
  · fin_cases i
    · change rawSlabCutoff a δ (coordinateRepresentative 1 q) *
        u.gradient (microSlabCoordinates a r k (q 0) (circleRepresentative (q 1))) (0,c) -
        slabPhysicalValue a r k u.gradient q (0,c) = _
      rw [hmap]
      simp only [cutoffMismatchValue, aspectErrorValue, derivativeErrorValue, slabValue,
        slabPhysicalValue, hq, ite_true]
      norm_num [Fin.ext_iff]
      ring
    · change (((k : ℝ) / (a * r)) * rawSlabCutoff a δ (coordinateRepresentative 1 q) *
        u.gradient (microSlabCoordinates a r k (q 0) (circleRepresentative (q 1))) (1,c) +
        (r : ℝ)⁻¹ * rawSlabCutoffDerivative a δ (coordinateRepresentative 1 q) *
        u.potential c (microSlabCoordinates a r k (q 0) (circleRepresentative (q 1)))) -
        slabPhysicalValue a r k u.gradient q (1,c) = _
      rw [hmap]
      simp only [cutoffMismatchValue, aspectErrorValue, derivativeErrorValue, slabValue,
        slabPhysicalValue, hq, ite_true]
      norm_num [Fin.ext_iff]
      ring
  · have hz : rawSlabCutoff a δ (coordinateRepresentative 1 q) = 0 :=
      rawSlabCutoff_zero_right hδ (by linarith [le_of_not_gt hq])
    have hdz := rawSlabCutoffDerivative_zero_of_zero hz
    fin_cases i <;>
      simp [localizedPotentialGradient, liftSlabFamily, localizedRawGradient,
        ← coordinateRepresentative_eq_circleRepresentative, cutoffMismatchValue, aspectErrorValue,
        derivativeErrorValue, slabValue, slabPhysicalValue, hq, hz, hdz]

theorem regularPotential_component_field_coe (u : RegularPotential) (i : Fin 2) (c : Fin 16) :
    componentField i c u.field =ᵐ[domainMeasure] fun q => u.gradient q (i,c) := by
  rw [RegularPotential.field, HierarchicalLaminates.Fourier.componentField_continuousField]
  exact ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure _

theorem slabField_component_coe (a : ℝ) (r k : ℕ) (u : RegularPotential)
    (i : Fin 2) (c : Fin 16) :
    componentField i c (u.slabField a r k) =ᵐ[domainMeasure]
      fun q => slabPhysicalValue a r k u.gradient q (i,c) := by
  filter_upwards [(EuclideanSpace.proj (𝕜 := ℝ) (i,c)).coeFn_compLpL (u.slabField a r k),
    u.slabField_coe a r k] with q hp hs
  change (EuclideanSpace.proj (𝕜 := ℝ) (i,c)).compLpL 2 domainMeasure
    (u.slabField a r k) q = _
  rw [hp, hs]
  rfl

theorem localizedPotential_component_error {a δ : ℝ} (ha₀ : 0 < a) (ha : a ≤ 1)
    (hδ : 0 < δ) {r : ℕ} (hr : 0 < r) (k : ℕ) (u : RegularPotential)
    (i : Fin 2) (c : Fin 16) :
    componentField i c ((localizedPotential ha₀ ha hδ hr k u).field - u.slabField a r k) =
      cutoffMismatchField a δ r k u i c + aspectErrorField a δ r k u i c +
        derivativeErrorField a δ r k u i c := by
  rw [map_sub]
  apply Lp.ext
  filter_upwards [regularPotential_component_field_coe (localizedPotential ha₀ ha hδ hr k u) i c,
    slabField_component_coe a r k u i c,
    boundedScalarField_coe _ _ _ (cutoffMismatchValue_bound a δ r k u i c),
    boundedScalarField_coe _ _ _ (aspectErrorValue_bound a δ r k u i c),
    boundedScalarField_coe _ _ _ (derivativeErrorValue_bound a δ r k u i c),
    Lp.coeFn_sub (componentField i c (localizedPotential ha₀ ha hδ hr k u).field)
      (componentField i c (u.slabField a r k)),
    Lp.coeFn_add (cutoffMismatchField a δ r k u i c) (aspectErrorField a δ r k u i c),
    Lp.coeFn_add (cutoffMismatchField a δ r k u i c + aspectErrorField a δ r k u i c)
      (derivativeErrorField a δ r k u i c)] with q hl hs hA hB hD hsub hab habd
  simp only [Pi.sub_apply, Pi.add_apply] at hsub hab habd
  change cutoffMismatchField a δ r k u i c q = _ at hA
  change aspectErrorField a δ r k u i c q = _ at hB
  change derivativeErrorField a δ r k u i c q = _ at hD
  rw [hsub, habd, hab]
  rw [hl, hs, hA, hB, hD]
  exact localizedPotential_component_error_value ha hδ r k u i c q

end HierarchicalLaminates.Composition
