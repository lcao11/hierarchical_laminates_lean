module

public import HierarchicalLaminates.Binary.HorizontalWeakDerivative

/-!
# Uniform consistency of the sampled profile

Sampling changes only the vertical coordinate, by less than one strip height.
The resulting pointwise and L² errors are bounded by `C/N`.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Binary

open MeasureTheory Set HierarchicalLaminates.Periodic HierarchicalLaminates.Fourier

def verticalProfileDerivative : C(Domain, ℝ) :=
  (-(Real.pi / 3)) • (sineKernel (0, 1) + (3 : ℝ) • sineKernel (1, 3))

theorem cosineProfile_hasDerivAt_vertical (q : Domain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => cosineProfile (coordinateFlow 1 q s))
      (verticalProfileDerivative (coordinateFlow 1 q t)) t := by
  have ha := hasDerivAt_cosineKernel_flow_at (1, 0) 1 q t
  have hb := hasDerivAt_cosineKernel_flow_at (0, 1) 1 q t
  have hc := hasDerivAt_cosineKernel_flow_at (1, 3) 1 q t
  have hd := (hasDerivAt_const t (1 / 2 : ℝ)).add ((ha.add hb |>.add hc).const_mul (1 / 6 : ℝ))
  convert hd using 1
  · funext s
    simp only [cosineProfile, ContinuousMap.add_apply, ContinuousMap.smul_apply,
      ContinuousMap.one_apply, smul_eq_mul, mul_one, Pi.add_apply]
  · norm_num [verticalProfileDerivative, frequencyVector]
    ring

theorem cosineProfile_vertical_lipschitz (q : Domain) :
    LipschitzWith ‖verticalProfileDerivative‖₊
      (fun s : ℝ => cosineProfile (coordinateFlow 1 q s)) := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro s
    exact (cosineProfile_hasDerivAt_vertical q s).differentiableAt
  · intro s
    rw [(cosineProfile_hasDerivAt_vertical q s).deriv]
    exact_mod_cast verticalProfileDerivative.norm_coe_le_norm (coordinateFlow 1 q s)

/-- A sampled point and its strip point differ vertically by less than `1/N`. -/
theorem sampledPoint_vertical_flow {N : ℕ} (hN : 0 < N) (q : Domain) :
    coordinateFlow 1 (sampledPoint N q) (stripCoordinate N q / N) = q := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have heq : (stripIndex N q : ℝ) / N + stripCoordinate N q / N =
      coordinateRepresentative 1 q := by
    unfold stripCoordinate
    field_simp
    ring
  ext i
  fin_cases i
  · simp [coordinateFlow, sampledPoint]
  · change (((stripIndex N q : ℝ) / N : ℝ) : UnitAddCircle) +
      (((stripCoordinate N q / N) : ℝ) : UnitAddCircle) = q 1
    rw [← AddCircle.coe_add, heq]
    exact AddCircle.coe_equivIco

theorem sampledProfileError_abs_le {N : ℕ} (hN : 0 < N) (q : Domain) :
    |sampledFraction N q - cosineProfile q| ≤ ‖verticalProfileDerivative‖ / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hτ := stripCoordinate_mem N q
  have h := (cosineProfile_vertical_lipschitz (sampledPoint N q)).dist_le_mul
    0 (stripCoordinate N q / N)
  rw [coordinateFlow_zero, sampledPoint_vertical_flow hN q] at h
  simp only [Real.dist_eq, zero_sub, abs_neg] at h
  change |sampledFraction N q - cosineProfile q| ≤
    ‖verticalProfileDerivative‖ * |stripCoordinate N q / N| at h
  apply h.trans
  rw [abs_of_nonneg (div_nonneg hτ.1 hNr.le), div_eq_mul_inv, div_eq_mul_inv]
  calc
    _ ≤ ‖verticalProfileDerivative‖ * (1 * (N : ℝ)⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact mul_le_mul_of_nonneg_right (le_of_lt hτ.2) (inv_nonneg.mpr hNr.le)
    _ = _ := by ring

def sampledProfileError (N : ℕ) (q : Domain) : ℝ := sampledFraction N q - cosineProfile q

theorem sampledProfileError_measurable (N : ℕ) : Measurable (sampledProfileError N) :=
  (sampledFraction_measurable N).sub cosineProfile.continuous.measurable

theorem sampledProfileError_memLp {N : ℕ} (hN : 0 < N) :
    MemLp (sampledProfileError N) 2 domainMeasure := by
  apply MemLp.of_bound (sampledProfileError_measurable N).aestronglyMeasurable
    (‖verticalProfileDerivative‖ / N)
  exact Filter.Eventually.of_forall fun q => by
    simpa only [Real.norm_eq_abs, sampledProfileError] using sampledProfileError_abs_le hN q

def sampledProfileErrorField (N : ℕ) (hN : 0 < N) : ScalarField :=
  (sampledProfileError_memLp hN).toLp (sampledProfileError N)

theorem sampledProfileErrorField_norm_le {N : ℕ} (hN : 0 < N) :
    ‖sampledProfileErrorField N hN‖ ≤ ‖verticalProfileDerivative‖ / N := by
  apply scalarField_norm_le (by positivity)
  filter_upwards [MemLp.coeFn_toLp (sampledProfileError_memLp hN)] with q hq
  change ‖(sampledProfileError_memLp hN).toLp (sampledProfileError N) q‖ ≤ _
  rw [hq, Real.norm_eq_abs]
  exact sampledProfileError_abs_le hN q

end HierarchicalLaminates.Binary
