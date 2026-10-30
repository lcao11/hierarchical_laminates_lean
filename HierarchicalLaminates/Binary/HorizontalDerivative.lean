module

public import HierarchicalLaminates.Binary.VerticalWeakDerivative
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Horizontal derivative of the sampled-width primitive
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Binary

open MeasureTheory Set HierarchicalLaminates.Periodic HierarchicalLaminates.Fourier

local notation "μcircle" => AddCircle.haarAddCircle (T := (1 : ℝ))

local instance circleHaar_nullSingleton : NullSingletonClass μcircle where
  measure_singleton x := by
    have hv : (volume : Measure UnitAddCircle) {x} = 0 := by
      rw [← Metric.closedBall_zero, AddCircle.volume_closedBall]
      norm_num
    rw [AddCircle.volume_eq_smul_haarAddCircle] at hv
    simpa only [ENNReal.ofReal_one, one_smul] using hv

def horizontalProfileDerivative : C(Domain, ℝ) :=
  (-(Real.pi / 3)) • (sineKernel (1, 0) + sineKernel (1, 3))

theorem cosineProfile_hasDerivAt_horizontal (q : Domain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => cosineProfile (coordinateFlow 0 q s))
      (horizontalProfileDerivative (coordinateFlow 0 q t)) t := by
  have ha := hasDerivAt_cosineKernel_flow_at (1, 0) 0 q t
  have hb := hasDerivAt_cosineKernel_flow_at (0, 1) 0 q t
  have hc := hasDerivAt_cosineKernel_flow_at (1, 3) 0 q t
  have hd := (hasDerivAt_const t (1 / 2 : ℝ)).add ((ha.add hb |>.add hc).const_mul (1 / 6 : ℝ))
  convert hd using 1
  · funext s
    simp only [cosineProfile, ContinuousMap.add_apply, ContinuousMap.smul_apply,
      ContinuousMap.one_apply, smul_eq_mul, mul_one, Pi.add_apply]
  · simp only [horizontalProfileDerivative, ContinuousMap.smul_apply,
      ContinuousMap.add_apply, smul_eq_mul, frequencyVector, Matrix.cons_val_zero,
      Int.cast_one, Int.cast_zero]
    ring

theorem stripIndex_horizontal_flow (N : ℕ) (q : Domain) (s : ℝ) :
    stripIndex N (coordinateFlow 0 q s) = stripIndex N q := by
  unfold stripIndex coordinateRepresentative
  simp [coordinateFlow]

theorem stripCoordinate_horizontal_flow (N : ℕ) (q : Domain) (s : ℝ) :
    stripCoordinate N (coordinateFlow 0 q s) = stripCoordinate N q := by
  unfold stripCoordinate coordinateRepresentative
  rw [stripIndex_horizontal_flow]
  simp [coordinateFlow]

theorem sampledPoint_horizontal_flow (N : ℕ) (q : Domain) (s : ℝ) :
    sampledPoint N (coordinateFlow 0 q s) = coordinateFlow 0 (sampledPoint N q) s := by
  unfold sampledPoint
  rw [stripIndex_horizontal_flow]
  ext i
  fin_cases i <;> simp [coordinateFlow]

theorem binaryPrimitive_horizontal_flow (N : ℕ) (q : Domain) (s : ℝ) :
    binaryPrimitive N (coordinateFlow 0 q s) =
      stripePrimitive (1 / (N : ℝ)) (stripCoordinate N q)
        (cosineProfile (coordinateFlow 0 (sampledPoint N q) s)) := by
  unfold binaryPrimitive sampledFraction
  rw [stripCoordinate_horizontal_flow, sampledPoint_horizontal_flow]

def binaryHorizontalDerivative (N : ℕ) (q : Domain) : ℝ :=
  ((1 / (N : ℝ)) * (stripeIndicator (sampledFraction N q) (stripCoordinate N q) -
    stripCoordinate N q)) * horizontalProfileDerivative (sampledPoint N q)

theorem binaryHorizontalDerivative_measurable (N : ℕ) :
    Measurable (binaryHorizontalDerivative N) := by
  have hind : Measurable (fun q => stripeIndicator (sampledFraction N q) (stripCoordinate N q)) :=
    Measurable.ite
      (measurableSet_lt (sampledFraction_measurable N) (stripCoordinate_measurable N))
      measurable_const measurable_const
  exact (measurable_const.mul (hind.sub (stripCoordinate_measurable N))).mul
    (horizontalProfileDerivative.continuous.measurable.comp (sampledPoint_measurable N))

theorem binaryHorizontalDerivative_abs_le {N : ℕ} (hN : 0 < N) (q : Domain) :
    |binaryHorizontalDerivative N q| ≤ (1 / (N : ℝ)) * ‖horizontalProfileDerivative‖ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hτ := stripCoordinate_mem N q
  have hcoeff := primitive_derivative_bound (one_div_nonneg.mpr hNr.le)
    (show stripCoordinate N q ∈ Icc (0 : ℝ) 1 from ⟨hτ.1, le_of_lt hτ.2⟩)
    (tau := sampledFraction N q)
  unfold binaryHorizontalDerivative
  rw [abs_mul]
  exact mul_le_mul hcoeff (horizontalProfileDerivative.norm_coe_le_norm _)
    (abs_nonneg _) (one_div_nonneg.mpr hNr.le)

/-- The classical horizontal derivative away from the moving interface. -/
theorem binaryPrimitive_hasDerivAt_horizontal {N : ℕ} (q : Domain)
    (hne : sampledFraction N q ≠ stripCoordinate N q) :
    HasDerivAt (fun s : ℝ => binaryPrimitive N (coordinateFlow 0 q s))
      (binaryHorizontalDerivative N q) 0 := by
  have houter := primitive_width_derivative (1 / (N : ℝ))
    (stripCoordinate N q) (sampledFraction N q) hne
  have hinner := cosineProfile_hasDerivAt_horizontal (sampledPoint N q) 0
  have hpoint : cosineProfile (coordinateFlow 0 (sampledPoint N q) 0) =
      sampledFraction N q := by
    rw [coordinateFlow_zero]
    rfl
  have houterAt : HasDerivAt (fun s => stripePrimitive (1 / (N : ℝ)) (stripCoordinate N q) s)
      ((1 / (N : ℝ)) * (stripeIndicator (sampledFraction N q) (stripCoordinate N q) -
        stripCoordinate N q)) (cosineProfile (coordinateFlow 0 (sampledPoint N q) 0)) := by
    rw [hpoint]
    exact houter
  have h := houterAt.comp 0 hinner
  convert h using 1
  · funext s
    exact binaryPrimitive_horizontal_flow N q s
  · rw [coordinateFlow_zero]
    rfl

/-- Each vertical fiber of the moving interface is contained in a countable explicit set. -/
theorem interface_fiber_countable {N : ℕ} (hN : 0 < N) (x : UnitAddCircle) :
    {y : UnitAddCircle | sampledFraction N ![x, y] = stripCoordinate N ![x, y]}.Countable := by
  let points : ℤ → UnitAddCircle := fun k =>
    ((((k : ℝ) + cosineProfile ![x, (((k : ℝ) / N : ℝ) : UnitAddCircle)]) / N : ℝ) : UnitAddCircle)
  apply (Set.countable_range points).mono
  intro y hy
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  refine ⟨stripIndex N ![x, y], ?_⟩
  have hyreal : ((stripIndex N ![x, y] : ℝ) +
      cosineProfile ![x, (((stripIndex N ![x, y] : ℝ) / N : ℝ) : UnitAddCircle)]) / N =
      coordinateRepresentative 1 ![x, y] := by
    change sampledFraction N ![x, y] = stripCoordinate N ![x, y] at hy
    unfold stripCoordinate at hy
    change cosineProfile ![x, (((stripIndex N ![x, y] : ℝ) / N : ℝ) : UnitAddCircle)] =
      (N : ℝ) * coordinateRepresentative 1 ![x, y] - (stripIndex N ![x, y] : ℝ) at hy
    apply (div_eq_iff hNr).mpr
    linarith
  change (((((stripIndex N ![x, y] : ℝ) +
    cosineProfile ![x, (((stripIndex N ![x, y] : ℝ) / N : ℝ) : UnitAddCircle)]) / N) : ℝ) : UnitAddCircle) = y
  rw [hyreal]
  exact AddCircle.coe_equivIco

/-- The complete moving interface has zero product Haar measure. -/
theorem binaryPrimitive_horizontal_interface_ae {N : ℕ} (hN : 0 < N) :
    ∀ᵐ q ∂domainMeasure, sampledFraction N q ≠ stripCoordinate N q := by
  have hprod : ∀ᵐ p : UnitAddCircle × UnitAddCircle ∂(μcircle).prod μcircle,
      sampledFraction N ![p.1, p.2] ≠ stripCoordinate N ![p.1, p.2] := by
    have hm : Measurable (fun p : UnitAddCircle × UnitAddCircle => ![p.1, p.2]) := by
      apply Measurable.of_eval
      intro i
      fin_cases i
      · exact measurable_fst
      · exact measurable_snd
    have heq : MeasurableSet {p : UnitAddCircle × UnitAddCircle |
        sampledFraction N ![p.1, p.2] = stripCoordinate N ![p.1, p.2]} :=
      measurableSet_eq_fun ((sampledFraction_measurable N).comp hm)
        ((stripCoordinate_measurable N).comp hm)
    apply (Measure.ae_prod_iff_ae_ae
      (p := fun p : UnitAddCircle × UnitAddCircle =>
        sampledFraction N ![p.1, p.2] ≠ stripCoordinate N ![p.1, p.2]) heq.compl).mpr
    apply Filter.Eventually.of_forall
    intro x
    exact measure_eq_zero_iff_ae_notMem.mp ((interface_fiber_countable hN x).measure_zero μcircle)
  have h := (measurePreserving_finTwoArrow μcircle).quasiMeasurePreserving.ae hprod
  change ∀ᵐ q ∂domainMeasure,
    sampledFraction N ![(MeasurableEquiv.finTwoArrow q).1, (MeasurableEquiv.finTwoArrow q).2] ≠
    stripCoordinate N ![(MeasurableEquiv.finTwoArrow q).1, (MeasurableEquiv.finTwoArrow q).2] at h
  have hη (q : Domain) :
      ![(MeasurableEquiv.finTwoArrow q).1, (MeasurableEquiv.finTwoArrow q).2] = q := by
    ext i
    fin_cases i <;> rfl
  simpa only [hη] using h

/-- A uniform Lipschitz bound across the kink, used for dominated differentiation. -/
theorem stripePrimitive_width_dist_le {h τ : ℝ} (hh : 0 ≤ h) (hτ : τ ∈ Icc (0 : ℝ) 1)
    (a b : ℝ) :
    dist (stripePrimitive h τ a) (stripePrimitive h τ b) ≤ (2 * h) * dist a b := by
  have hmin := (LipschitzWith.id.const_min τ).dist_le_mul a b
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hmin
  rw [Real.dist_eq]
  have heq : stripePrimitive h τ a - stripePrimitive h τ b =
      h * ((min τ a - min τ b) - τ * (a - b)) := by
    unfold stripePrimitive
    ring
  rw [heq, abs_mul, abs_of_nonneg hh]
  calc
    h * |(min τ a - min τ b) - τ * (a - b)| ≤
        h * (|min τ a - min τ b| + |τ * (a - b)|) := by
      gcongr
      exact abs_sub _ _
    _ ≤ h * (|a - b| + |a - b|) := by
      rw [abs_mul, abs_of_nonneg hτ.1]
      apply mul_le_mul_of_nonneg_left _ hh
      apply add_le_add (by simpa only [id_eq] using hmin)
      exact (mul_le_mul_of_nonneg_right hτ.2 (abs_nonneg (a - b))).trans_eq (one_mul _)
    _ = (2 * h) * dist a b := by rw [Real.dist_eq]; ring

theorem cosineProfile_horizontal_lipschitz (q : Domain) :
    LipschitzWith ‖horizontalProfileDerivative‖₊
      (fun s : ℝ => cosineProfile (coordinateFlow 0 q s)) := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro s
    exact (cosineProfile_hasDerivAt_horizontal q s).differentiableAt
  · intro s
    rw [(cosineProfile_hasDerivAt_horizontal q s).deriv]
    exact_mod_cast horizontalProfileDerivative.norm_coe_le_norm (coordinateFlow 0 q s)

theorem smoothTest_horizontal_lipschitz (test : SmoothTest) (q : Domain) :
    LipschitzWith ‖test.derivative 0‖₊
      (fun s : ℝ => test.value (coordinateFlow 0 q s)) := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro s
    exact (smoothTest_hasDerivAt_flow test 0 q s).differentiableAt
  · intro s
    rw [(smoothTest_hasDerivAt_flow test 0 q s).deriv]
    exact_mod_cast (test.derivative 0).norm_coe_le_norm (coordinateFlow 0 q s)

theorem binaryPrimitive_horizontal_dist_le {N : ℕ} (hN : 0 < N) (q : Domain) (s t : ℝ) :
    dist (binaryPrimitive N (coordinateFlow 0 q s)) (binaryPrimitive N (coordinateFlow 0 q t)) ≤
      (2 / (N : ℝ)) * ‖horizontalProfileDerivative‖ * dist s t := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hτ := stripCoordinate_mem N q
  have h := stripePrimitive_width_dist_le (one_div_nonneg.mpr hNr.le)
    (show stripCoordinate N q ∈ Icc (0 : ℝ) 1 from ⟨hτ.1, le_of_lt hτ.2⟩)
    (cosineProfile (coordinateFlow 0 (sampledPoint N q) s))
    (cosineProfile (coordinateFlow 0 (sampledPoint N q) t))
  rw [← binaryPrimitive_horizontal_flow, ← binaryPrimitive_horizontal_flow] at h
  calc
    _ ≤ (2 * (1 / (N : ℝ))) *
        dist (cosineProfile (coordinateFlow 0 (sampledPoint N q) s))
          (cosineProfile (coordinateFlow 0 (sampledPoint N q) t)) := h
    _ ≤ (2 * (1 / (N : ℝ))) * (‖horizontalProfileDerivative‖ * dist s t) := by
      gcongr
      exact (cosineProfile_horizontal_lipschitz (sampledPoint N q)).dist_le_mul s t
    _ = _ := by ring

end HierarchicalLaminates.Binary
