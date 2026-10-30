module

public import HierarchicalLaminates.Binary.HorizontalDerivative

/-!
# The horizontal distribution identity on the torus

The moving interface has measure zero. A uniform horizontal Lipschitz bound
permits dominated differentiation of the translation-invariant integral.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Binary

open MeasureTheory Set HierarchicalLaminates.Periodic HierarchicalLaminates.Fourier
open scoped Topology

local instance : Measure.IsAddRightInvariant domainMeasure := by
  dsimp [domainMeasure]
  infer_instance

theorem real_mul_dist_le (a b c d : ℝ) :
    dist (a * b) (c * d) ≤ |a| * dist b d + dist a c * |d| := by
  simp only [Real.dist_eq]
  have heq : a * b - c * d = a * (b - d) + (a - c) * d := by ring
  rw [heq]
  exact (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_mul])

def horizontalProductLipschitzBound (N : ℕ) (test : SmoothTest) : ℝ :=
  (1 / (4 * (N : ℝ))) * ‖test.derivative 0‖ +
    (2 / (N : ℝ)) * ‖horizontalProfileDerivative‖ * ‖test.value‖

theorem horizontalProductLipschitzBound_nonneg {N : ℕ} (hN : 0 < N) (test : SmoothTest) :
    0 ≤ horizontalProductLipschitzBound N test := by
  unfold horizontalProductLipschitzBound
  positivity

theorem binaryPrimitive_horizontal_product_dist_le {N : ℕ} (hN : 0 < N)
    (test : SmoothTest) (q : Domain) (s t : ℝ) :
    dist (binaryPrimitive N (coordinateFlow 0 q s) * test.value (coordinateFlow 0 q s))
      (binaryPrimitive N (coordinateFlow 0 q t) * test.value (coordinateFlow 0 q t)) ≤
        horizontalProductLipschitzBound N test * dist s t := by
  have hws : |binaryPrimitive N (coordinateFlow 0 q s)| ≤ 1 / (4 * (N : ℝ)) := by
    rw [abs_of_nonneg (binaryPrimitive_bounds hN _).1]
    exact (binaryPrimitive_bounds hN _).2
  have hφt : |test.value (coordinateFlow 0 q t)| ≤ ‖test.value‖ :=
    test.value.norm_coe_le_norm _
  have hφdist := (smoothTest_horizontal_lipschitz test q).dist_le_mul s t
  have hwdist := binaryPrimitive_horizontal_dist_le hN q s t
  calc
    _ ≤ |binaryPrimitive N (coordinateFlow 0 q s)| *
        dist (test.value (coordinateFlow 0 q s)) (test.value (coordinateFlow 0 q t)) +
        dist (binaryPrimitive N (coordinateFlow 0 q s)) (binaryPrimitive N (coordinateFlow 0 q t)) *
        |test.value (coordinateFlow 0 q t)| := real_mul_dist_le _ _ _ _
    _ ≤ (1 / (4 * (N : ℝ))) * (‖test.derivative 0‖ * dist s t) +
        ((2 / (N : ℝ)) * ‖horizontalProfileDerivative‖ * dist s t) * ‖test.value‖ := by
      apply add_le_add
      · exact mul_le_mul hws hφdist dist_nonneg (by positivity)
      · exact mul_le_mul hwdist hφt (abs_nonneg _) (by positivity)
    _ = _ := by unfold horizontalProductLipschitzBound; ring

theorem binaryHorizontalDerivative_test_product_bound {N : ℕ} (hN : 0 < N)
    (test : SmoothTest) (q : Domain) :
    ‖binaryHorizontalDerivative N q * test.value q‖ ≤
      ((1 / (N : ℝ)) * ‖horizontalProfileDerivative‖) * ‖test.value‖ := by
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul (binaryHorizontalDerivative_abs_le hN q)
    (test.value.norm_coe_le_norm q) (norm_nonneg _) (by positivity)

theorem binaryPrimitive_horizontal_test_product_bound {N : ℕ} (hN : 0 < N)
    (test : SmoothTest) (q : Domain) :
    ‖binaryPrimitive N q * test.derivative 0 q‖ ≤
      (1 / (4 * (N : ℝ))) * ‖test.derivative 0‖ := by
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (binaryPrimitive_bounds hN q).1]
  exact mul_le_mul (binaryPrimitive_bounds hN q).2
    ((test.derivative 0).norm_coe_le_norm q) (norm_nonneg _) (by positivity)

/-- The horizontal weak derivative against every smooth periodic test. -/
theorem binaryPrimitive_horizontal_weakDerivative {N : ℕ} (hN : 0 < N) (test : SmoothTest) :
    (∫ q, binaryHorizontalDerivative N q * test.value q ∂domainMeasure) =
      -(∫ q, binaryPrimitive N q * test.derivative 0 q ∂domainMeasure) := by
  let F : ℝ → Domain → ℝ := fun s q =>
    binaryPrimitive N (coordinateFlow 0 q s) * test.value (coordinateFlow 0 q s)
  let F' : Domain → ℝ := fun q =>
    binaryHorizontalDerivative N q * test.value q + binaryPrimitive N q * test.derivative 0 q
  have hFmeas (s : ℝ) : Measurable (F s) := by
    apply ((binaryPrimitive_measurable N).mul test.value.continuous.measurable).comp
    exact (continuous_id.add continuous_const).measurable
  have hF0bound (q : Domain) : ‖F 0 q‖ ≤
      (1 / (4 * (N : ℝ))) * ‖test.value‖ := by
    change ‖binaryPrimitive N (coordinateFlow 0 q 0) * test.value (coordinateFlow 0 q 0)‖ ≤ _
    rw [coordinateFlow_zero, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (binaryPrimitive_bounds hN q).1]
    exact mul_le_mul (binaryPrimitive_bounds hN q).2
      (test.value.norm_coe_le_norm q) (norm_nonneg _) (by positivity)
  have hFint : Integrable (F 0) domainMeasure :=
    Integrable.of_bound (hFmeas 0).aestronglyMeasurable _ (Filter.Eventually.of_forall hF0bound)
  have hF'meas : Measurable F' :=
    ((binaryHorizontalDerivative_measurable N).mul test.value.continuous.measurable).add
      ((binaryPrimitive_measurable N).mul (test.derivative 0).continuous.measurable)
  have hLip : ∀ᵐ q ∂domainMeasure,
      LipschitzOnWith (Real.nnabs (horizontalProductLipschitzBound N test))
        (F · q) Set.univ := by
    apply Filter.Eventually.of_forall
    intro q
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    change dist (F s q) (F t q) ≤
      (Real.nnabs (horizontalProductLipschitzBound N test) : ℝ) * dist s t
    rw [Real.coe_nnabs, abs_of_nonneg (horizontalProductLipschitzBound_nonneg hN test)]
    exact binaryPrimitive_horizontal_product_dist_le hN test q s t
  have hdiff : ∀ᵐ q ∂domainMeasure, HasDerivAt (F · q) (F' q) 0 := by
    filter_upwards [binaryPrimitive_horizontal_interface_ae hN] with q hq
    have hd := (binaryPrimitive_hasDerivAt_horizontal q hq).mul
      (smoothTest_hasDerivAt_flow test 0 q 0)
    simp only [coordinateFlow_zero] at hd
    convert hd using 1
  have hint := hasDerivAt_integral_of_dominated_loc_of_lip
    (F := F) (F' := F') (μ := domainMeasure) (bound := fun _ => horizontalProductLipschitzBound N test)
    (s := Set.univ) (x₀ := (0 : ℝ)) Filter.univ_mem
    (Filter.Eventually.of_forall fun s => (hFmeas s).aestronglyMeasurable)
    hFint hF'meas.aestronglyMeasurable hLip (integrable_const _) hdiff
  have htranslation : (fun s : ℝ => ∫ q, F s q ∂domainMeasure) =
      (fun _ : ℝ => ∫ q, binaryPrimitive N q * test.value q ∂domainMeasure) := by
    funext s
    exact integral_add_right_eq_self (fun q => binaryPrimitive N q * test.value q)
      (Pi.single 0 (s : UnitAddCircle))
  have hz := hint.2
  rw [htranslation] at hz
  have hzero := hz.unique (hasDerivAt_const (0 : ℝ)
    (∫ q, binaryPrimitive N q * test.value q ∂domainMeasure))
  change (∫ q, binaryHorizontalDerivative N q * test.value q +
    binaryPrimitive N q * test.derivative 0 q ∂domainMeasure) = 0 at hzero
  have hleft : Integrable (fun q => binaryHorizontalDerivative N q * test.value q) domainMeasure :=
    Integrable.of_bound ((binaryHorizontalDerivative_measurable N).mul
      test.value.continuous.measurable).aestronglyMeasurable _
      (Filter.Eventually.of_forall (binaryHorizontalDerivative_test_product_bound hN test))
  have hright : Integrable (fun q => binaryPrimitive N q * test.derivative 0 q) domainMeasure :=
    Integrable.of_bound ((binaryPrimitive_measurable N).mul
      (test.derivative 0).continuous.measurable).aestronglyMeasurable _
      (Filter.Eventually.of_forall (binaryPrimitive_horizontal_test_product_bound hN test))
  rw [integral_add hleft hright] at hzero
  exact eq_neg_of_add_eq_zero_left hzero

theorem binaryHorizontalDerivative_memLp {N : ℕ} (hN : 0 < N) :
    MemLp (binaryHorizontalDerivative N) 2 domainMeasure := by
  apply MemLp.of_bound (binaryHorizontalDerivative_measurable N).aestronglyMeasurable
    ((1 / (N : ℝ)) * ‖horizontalProfileDerivative‖)
  exact Filter.Eventually.of_forall fun q => by
    simpa only [Real.norm_eq_abs] using binaryHorizontalDerivative_abs_le hN q

def binaryHorizontalDerivativeField (N : ℕ) (hN : 0 < N) : ScalarField :=
  (binaryHorizontalDerivative_memLp hN).toLp (binaryHorizontalDerivative N)

theorem binaryPrimitive_horizontal_weakPairing {N : ℕ} (hN : 0 < N) (test : SmoothTest) :
    inner ℝ (binaryHorizontalDerivativeField N hN) (continuousField test.value) =
      -inner ℝ (binaryPrimitiveField N hN) (continuousField (test.derivative 0)) := by
  have hleft : inner ℝ (binaryHorizontalDerivativeField N hN) (continuousField test.value) =
      ∫ q, binaryHorizontalDerivative N q * test.value q ∂domainMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (binaryHorizontalDerivative_memLp hN),
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure test.value] with q hd ht
    change inner ℝ ((binaryHorizontalDerivative_memLp hN).toLp (binaryHorizontalDerivative N) q)
      (ContinuousMap.toLp 2 domainMeasure ℝ test.value q) = _
    rw [hd, ht]
    simp only [Real.inner_apply]
  have hright : inner ℝ (binaryPrimitiveField N hN) (continuousField (test.derivative 0)) =
      ∫ q, binaryPrimitive N q * test.derivative 0 q ∂domainMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (binaryPrimitive_memLp hN),
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure (test.derivative 0)] with q hd ht
    change inner ℝ ((binaryPrimitive_memLp hN).toLp (binaryPrimitive N) q)
      (ContinuousMap.toLp 2 domainMeasure ℝ (test.derivative 0) q) = _
    rw [hd, ht]
    simp only [Real.inner_apply]
  rw [hleft, hright]
  exact binaryPrimitive_horizontal_weakDerivative hN test

/-- Both distributional derivatives of the stripe primitive in L². -/
def binaryPrimitiveDerivativeFields (N : ℕ) (hN : 0 < N) : Fin 2 → ScalarField :=
  ![binaryHorizontalDerivativeField N hN, binaryVerticalDerivativeField N]

theorem binaryPrimitive_weakPairing {N : ℕ} (hN : 0 < N) (i : Fin 2) (test : SmoothTest) :
    inner ℝ (binaryPrimitiveDerivativeFields N hN i) (continuousField test.value) =
      -inner ℝ (binaryPrimitiveField N hN) (continuousField (test.derivative i)) := by
  fin_cases i
  · exact binaryPrimitive_horizontal_weakPairing hN test
  · exact binaryPrimitive_vertical_weakPairing hN test

/-- On the normalized periodic cell, an almost everywhere scalar bound controls the L² norm. -/
theorem scalarField_norm_le {f : ScalarField} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ᵐ q ∂domainMeasure, ‖f q‖ ≤ C) : ‖f‖ ≤ C := by
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound hC hf

theorem binaryPrimitiveField_norm_le {N : ℕ} (hN : 0 < N) :
    ‖binaryPrimitiveField N hN‖ ≤ 1 / (4 * (N : ℝ)) := by
  apply scalarField_norm_le (by positivity)
  filter_upwards [MemLp.coeFn_toLp (binaryPrimitive_memLp hN)] with q hq
  change ‖(binaryPrimitive_memLp hN).toLp (binaryPrimitive N) q‖ ≤ _
  rw [hq, Real.norm_eq_abs, abs_of_nonneg (binaryPrimitive_bounds hN q).1]
  exact (binaryPrimitive_bounds hN q).2

theorem binaryHorizontalDerivativeField_norm_le {N : ℕ} (hN : 0 < N) :
    ‖binaryHorizontalDerivativeField N hN‖ ≤ (1 / (N : ℝ)) * ‖horizontalProfileDerivative‖ := by
  apply scalarField_norm_le (by positivity)
  filter_upwards [MemLp.coeFn_toLp (binaryHorizontalDerivative_memLp hN)] with q hq
  change ‖(binaryHorizontalDerivative_memLp hN).toLp (binaryHorizontalDerivative N) q‖ ≤ _
  rw [hq, Real.norm_eq_abs]
  exact binaryHorizontalDerivative_abs_le hN q

theorem binaryVerticalDerivativeField_norm_le (N : ℕ) :
    ‖binaryVerticalDerivativeField N‖ ≤ 1 := by
  apply scalarField_norm_le zero_le_one
  filter_upwards [MemLp.coeFn_toLp (binaryVerticalDerivative_memLp N)] with q hq
  change ‖(binaryVerticalDerivative_memLp N).toLp (binaryVerticalDerivative N) q‖ ≤ _
  rw [hq, Real.norm_eq_abs]
  exact binaryVerticalDerivative_abs_le N q

end HierarchicalLaminates.Binary
