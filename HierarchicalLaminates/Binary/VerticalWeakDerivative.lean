module

public import HierarchicalLaminates.Binary.Mean
public import HierarchicalLaminates.Binary.StripeWeakDerivative

/-!
# Global vertical weak derivative of the stripe primitive

The primitive vanishes at each strip edge, so the stripwise integration by
parts identities combine across the full periodic cell.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Binary

open MeasureTheory Set HierarchicalLaminates.Periodic HierarchicalLaminates.Fourier

local notation "μcircle" => AddCircle.haarAddCircle (T := (1 : ℝ))

def binaryVerticalDerivative (N : ℕ) (q : Domain) : ℝ :=
  binaryIndicator N q - sampledFraction N q

theorem binaryVerticalDerivative_measurable (N : ℕ) :
    Measurable (binaryVerticalDerivative N) :=
  (binaryIndicator_measurable N).sub (sampledFraction_measurable N)

theorem binaryVerticalDerivative_abs_le (N : ℕ) (q : Domain) :
    |binaryVerticalDerivative N q| ≤ 1 := by
  have hc := binaryIndicator_mem N q
  have ht := sampledFraction_mem N q
  unfold binaryVerticalDerivative
  exact abs_le.mpr ⟨by linarith [hc.1, ht.2], by linarith [hc.2, ht.1]⟩

theorem binaryPrimitive_pointInStrip {N k : ℕ} (hN : 0 < N) (hk : k < N)
    (x : UnitAddCircle) {τ : ℝ} (hτ : τ ∈ Ico (0 : ℝ) 1) :
    binaryPrimitive N (pointInStrip N k x τ) =
      stripePrimitive (1 / (N : ℝ)) τ (stripFraction N k x) := by
  unfold binaryPrimitive
  rw [stripCoordinate_pointInStrip hN hk x hτ]
  congr 1
  unfold sampledFraction sampledPoint stripFraction
  rw [stripIndex_pointInStrip hN hk x hτ]
  rfl

theorem binaryVerticalDerivative_pointInStrip {N k : ℕ} (hN : 0 < N) (hk : k < N)
    (x : UnitAddCircle) {τ : ℝ} (hτ : τ ∈ Ico (0 : ℝ) 1) :
    binaryVerticalDerivative N (pointInStrip N k x τ) =
      stripeIndicator τ (stripFraction N k x) - stripFraction N k x := by
  unfold binaryVerticalDerivative
  rw [binaryIndicator_pointInStrip hN hk x hτ]
  congr 1
  unfold sampledFraction sampledPoint stripFraction
  rw [stripIndex_pointInStrip hN hk x hτ]
  rfl

theorem integral_local_congr {f g : ℝ → ℝ}
    (hfg : ∀ τ ∈ Ico (0 : ℝ) 1, f τ = g τ) :
    (∫ τ in (0 : ℝ)..1, f τ) = ∫ τ in (0 : ℝ)..1, g τ := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Ico_eq_integral_Ioc, ← integral_Ico_eq_integral_Ioc]
  exact setIntegral_congr_fun measurableSet_Ico hfg

/-- Weak differentiation of torus functions in strip coordinates. -/
theorem binaryPrimitive_test_local_integrationByParts {N k : ℕ} (hN : 0 < N)
    (hk : k < N) (test : SmoothTest) (x : UnitAddCircle) :
    (∫ τ in (0 : ℝ)..1, binaryPrimitive N (pointInStrip N k x τ) *
      test.derivative 1 (pointInStrip N k x τ)) =
      -(∫ τ in (0 : ℝ)..1, binaryVerticalDerivative N (pointInStrip N k x τ) *
        test.value (pointInStrip N k x τ)) := by
  have hleft := integral_local_congr (fun τ hτ =>
    congrArg (fun a : ℝ => a * test.derivative 1 (pointInStrip N k x τ))
      (binaryPrimitive_pointInStrip hN hk x hτ))
  have hright := integral_local_congr (fun τ hτ =>
    congrArg (fun a : ℝ => a * test.value (pointInStrip N k x τ))
      (binaryVerticalDerivative_pointInStrip hN hk x hτ))
  rw [hleft, hright]
  exact stripePrimitive_test_vertical_integrationByParts hN test x

theorem integral_strip_substitution {N : ℕ} (hN : 0 < N) (k : ℕ) (f : ℝ → ℝ) :
    (∫ y in (k : ℝ) / N..((k : ℝ) + 1) / N, f y) =
      (1 / (N : ℝ)) * ∫ τ in (0 : ℝ)..1, f (((k : ℝ) + τ) / N) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have h := intervalIntegral.integral_comp_add_left (fun y : ℝ => f (y / N))
    (k : ℝ) (a := (0 : ℝ)) (b := (1 : ℝ))
  rw [intervalIntegral.integral_comp_div f hNr] at h
  simp only [add_zero, smul_eq_mul] at h
  rw [h]
  field_simp

theorem binaryPrimitive_test_strip_integrationByParts {N k : ℕ} (hN : 0 < N)
    (hk : k < N) (test : SmoothTest) (x : UnitAddCircle) :
    (∫ y in (k : ℝ) / N..((k : ℝ) + 1) / N,
      binaryPrimitive N ![x, (y : UnitAddCircle)] * test.derivative 1 ![x, (y : UnitAddCircle)]) =
      -(∫ y in (k : ℝ) / N..((k : ℝ) + 1) / N,
        binaryVerticalDerivative N ![x, (y : UnitAddCircle)] * test.value ![x, (y : UnitAddCircle)]) := by
  rw [integral_strip_substitution hN k, integral_strip_substitution hN k]
  change (1 / (N : ℝ)) *
    (∫ τ in (0 : ℝ)..1, binaryPrimitive N (pointInStrip N k x τ) *
      test.derivative 1 (pointInStrip N k x τ)) = _
  rw [binaryPrimitive_test_local_integrationByParts hN hk test x]
  rw [mul_neg]
  rfl

/-- Bounded measurable torus functions have integrable restrictions to vertical lines. -/
theorem bounded_height_intervalIntegrable {f : Domain → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ q, ‖f q‖ ≤ C) (x : UnitAddCircle) (a b : ℝ) :
    IntervalIntegrable (fun y : ℝ => f ![x, (y : UnitAddCircle)]) volume a b := by
  have hmeas : Measurable (fun y : ℝ => f ![x, (y : UnitAddCircle)]) := by
    apply hf.comp
    apply Measurable.of_eval
    intro i
    fin_cases i
    · exact measurable_const
    · exact AddCircle.measurable_mk'
  apply intervalIntegrable_iff.mpr
  apply IntegrableOn.of_bound (by simp only [Real.volume_uIoc]; exact ENNReal.ofReal_lt_top)
    hmeas.aestronglyMeasurable.restrict C
  exact Filter.Eventually.of_forall fun y => hC _

theorem binaryPrimitive_test_product_bound {N : ℕ} (hN : 0 < N) (test : SmoothTest)
    (q : Domain) :
    ‖binaryPrimitive N q * test.derivative 1 q‖ ≤
      (1 / (4 * (N : ℝ))) * ‖test.derivative 1‖ := by
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (binaryPrimitive_bounds hN q).1]
  exact mul_le_mul (binaryPrimitive_bounds hN q).2
    ((test.derivative 1).norm_coe_le_norm q) (norm_nonneg _) (by positivity)

theorem binaryVerticalDerivative_test_product_bound (N : ℕ) (test : SmoothTest)
    (q : Domain) :
    ‖binaryVerticalDerivative N q * test.value q‖ ≤ ‖test.value‖ := by
  rw [norm_mul, Real.norm_eq_abs]
  exact (mul_le_mul (binaryVerticalDerivative_abs_le N q)
    (test.value.norm_coe_le_norm q) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

/-- The vertical distribution identity on the full height interval. -/
theorem binaryPrimitive_test_height_integrationByParts {N : ℕ} (hN : 0 < N)
    (test : SmoothTest) (x : UnitAddCircle) :
    (∫ y in (0 : ℝ)..1,
      binaryPrimitive N ![x, (y : UnitAddCircle)] * test.derivative 1 ![x, (y : UnitAddCircle)]) =
      -(∫ y in (0 : ℝ)..1,
        binaryVerticalDerivative N ![x, (y : UnitAddCircle)] * test.value ![x, (y : UnitAddCircle)]) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hleft := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => (k : ℝ) / N) (n := N)
    (f := fun y : ℝ => binaryPrimitive N ![x, (y : UnitAddCircle)] *
      test.derivative 1 ![x, (y : UnitAddCircle)])
    (fun k hk => bounded_height_intervalIntegrable
      ((binaryPrimitive_measurable N).mul (test.derivative 1).continuous.measurable)
      (binaryPrimitive_test_product_bound hN test) x _ _)
  have hright := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => (k : ℝ) / N) (n := N)
    (f := fun y : ℝ => binaryVerticalDerivative N ![x, (y : UnitAddCircle)] *
      test.value ![x, (y : UnitAddCircle)])
    (fun k hk => bounded_height_intervalIntegrable
      ((binaryVerticalDerivative_measurable N).mul test.value.continuous.measurable)
      (binaryVerticalDerivative_test_product_bound N test) x _ _)
  simp only [Nat.cast_zero, zero_div, div_self hNr] at hleft hright
  rw [← hleft, ← hright, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  simpa only [Nat.cast_add, Nat.cast_one] using
    binaryPrimitive_test_strip_integrationByParts hN (Finset.mem_range.mp hk) test x

theorem bounded_domainIntegral_eq_iterated {f : Domain → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ q, ‖f q‖ ≤ C) :
    (∫ q, f q ∂domainMeasure) =
      ∫ x : UnitAddCircle, ∫ y : UnitAddCircle, f ![x, y] ∂μcircle ∂μcircle := by
  have hproduct : Integrable (fun p : UnitAddCircle × UnitAddCircle => f ![p.1, p.2])
      ((μcircle).prod μcircle) := by
    refine Integrable.of_bound ?_ C ?_
    · apply Measurable.aestronglyMeasurable
      apply hf.comp
      apply Measurable.of_eval
      intro i
      fin_cases i
      · exact measurable_fst
      · exact measurable_snd
    · exact Filter.Eventually.of_forall fun p => hC _
  have h := (measurePreserving_finTwoArrow μcircle).integral_comp'
    (fun p : UnitAddCircle × UnitAddCircle => f ![p.1, p.2])
  have hq : (fun q : Domain => f
      ![(MeasurableEquiv.finTwoArrow q).1, (MeasurableEquiv.finTwoArrow q).2]) = f := by
    funext q
    congr 1
    ext i
    fin_cases i <;> rfl
  rw [hq] at h
  change (∫ q, f q ∂domainMeasure) = _ at h
  rw [h]
  exact integral_prod _ hproduct

theorem circle_heightIntegral_eq (f : Domain → ℝ) (x : UnitAddCircle) :
    (∫ y : UnitAddCircle, f ![x, y] ∂μcircle) =
      ∫ y in (0 : ℝ)..1, f ![x, (y : UnitAddCircle)] := by
  have h := UnitAddCircle.intervalIntegral_preimage (0 : ℝ)
    (fun y : UnitAddCircle => f ![x, y])
  simp only [zero_add] at h
  rw [AddCircle.volume_eq_smul_haarAddCircle] at h
  simpa only [ENNReal.ofReal_one, one_smul] using h.symm

/-- The vertical weak derivative against every smooth periodic test. -/
theorem binaryPrimitive_vertical_weakDerivative {N : ℕ} (hN : 0 < N) (test : SmoothTest) :
    (∫ q, binaryVerticalDerivative N q * test.value q ∂domainMeasure) =
      -(∫ q, binaryPrimitive N q * test.derivative 1 q ∂domainMeasure) := by
  rw [bounded_domainIntegral_eq_iterated
    (f := fun q => binaryVerticalDerivative N q * test.value q)
    ((binaryVerticalDerivative_measurable N).mul test.value.continuous.measurable)
    (binaryVerticalDerivative_test_product_bound N test),
    bounded_domainIntegral_eq_iterated
    (f := fun q => binaryPrimitive N q * test.derivative 1 q)
    ((binaryPrimitive_measurable N).mul (test.derivative 1).continuous.measurable)
    (binaryPrimitive_test_product_bound hN test), ← integral_neg]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [circle_heightIntegral_eq
    (fun q => binaryVerticalDerivative N q * test.value q) x,
    circle_heightIntegral_eq (fun q => binaryPrimitive N q * test.derivative 1 q) x]
  exact (neg_eq_iff_eq_neg).mp
    (binaryPrimitive_test_height_integrationByParts hN test x).symm

/-- The stripe primitive belongs to the periodic L² space. -/
theorem binaryPrimitive_memLp {N : ℕ} (hN : 0 < N) :
    MemLp (binaryPrimitive N) 2 domainMeasure := by
  apply MemLp.of_bound (binaryPrimitive_measurable N).aestronglyMeasurable
    (1 / (4 * (N : ℝ)))
  apply Filter.Eventually.of_forall
  intro q
  rw [Real.norm_eq_abs, abs_of_nonneg (binaryPrimitive_bounds hN q).1]
  exact (binaryPrimitive_bounds hN q).2

theorem binaryVerticalDerivative_memLp (N : ℕ) :
    MemLp (binaryVerticalDerivative N) 2 domainMeasure := by
  apply MemLp.of_bound (binaryVerticalDerivative_measurable N).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun q => by
    simpa only [Real.norm_eq_abs] using binaryVerticalDerivative_abs_le N q

/-- An L² representative of the stripe primitive. -/
def binaryPrimitiveField (N : ℕ) (hN : 0 < N) : ScalarField :=
  (binaryPrimitive_memLp hN).toLp (binaryPrimitive N)

/-- An L² representative of the vertical derivative. -/
def binaryVerticalDerivativeField (N : ℕ) : ScalarField :=
  (binaryVerticalDerivative_memLp N).toLp (binaryVerticalDerivative N)

/-- The vertical component of the weak-gradient pairing. -/
theorem binaryPrimitive_vertical_weakPairing {N : ℕ} (hN : 0 < N) (test : SmoothTest) :
    inner ℝ (binaryVerticalDerivativeField N) (continuousField test.value) =
      -inner ℝ (binaryPrimitiveField N hN) (continuousField (test.derivative 1)) := by
  have hleft : inner ℝ (binaryVerticalDerivativeField N) (continuousField test.value) =
      ∫ q, binaryVerticalDerivative N q * test.value q ∂domainMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (binaryVerticalDerivative_memLp N),
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure test.value] with q hd ht
    change inner ℝ ((binaryVerticalDerivative_memLp N).toLp (binaryVerticalDerivative N) q)
      (ContinuousMap.toLp 2 domainMeasure ℝ test.value q) = _
    rw [hd, ht]
    simp only [Real.inner_apply]
  have hright : inner ℝ (binaryPrimitiveField N hN) (continuousField (test.derivative 1)) =
      ∫ q, binaryPrimitive N q * test.derivative 1 q ∂domainMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (binaryPrimitive_memLp hN),
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure (test.derivative 1)] with q hd ht
    change inner ℝ ((binaryPrimitive_memLp hN).toLp (binaryPrimitive N) q)
      (ContinuousMap.toLp 2 domainMeasure ℝ (test.derivative 1) q) = _
    rw [hd, ht]
    simp only [Real.inner_apply]
  rw [hleft, hright]
  exact binaryPrimitive_vertical_weakDerivative hN test

end HierarchicalLaminates.Binary
