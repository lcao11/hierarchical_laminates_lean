module

public import HierarchicalLaminates.Contrast.Response
public import HierarchicalLaminates.Fourier.WeightedRegularity

/-!
# Fourier moments and coordinate derivatives

For each fixed `0 < r < 2 / 3`, every polynomial coordinate-frequency moment
of `solution r` is summable. Each Neumann term has finite frequency support
whose radius grows linearly with its index, while its norm decays geometrically
with ratio `3 * r / 2`.

The synthesized coordinate derivative includes the angular-frequency factor
`2 * π` for the unit torus. `Contrast.Smoothness` uses these moments to prove
joint smoothness in both spatial variables, including mixed derivatives.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.Contrast

open Fourier

abbrev term (r : ℝ) (n : ℕ) : ReducedCoefficients := neumannTerm (contrastIteration r) (source r) n

theorem source_support (r : ℝ) : ∀ k,¬frequencyBox 1 k → source r k = 0 := by
  have hdelta : ∀ k,¬frequencyBox 0 k →
      (lp.single 1 (0,0) (ContinuousLinearMap.id ℝ ReducedSpace) : ReducedCoefficients) k = 0 := by
    intro k hk
    apply lp.single_apply_ne
    intro heq
    subst k
    exact hk (by norm_num [frequencyBox])
  intro k hk
  change r • profileMultiplication (lp.single 1 (0,0) (ContinuousLinearMap.id ℝ ReducedSpace)) k = 0
  rw [profileMultiplication_support 0 _ hdelta k hk]
  exact reducedOperator_smul_zero r

theorem term_support (r : ℝ) (n : ℕ) : ∀ k,¬frequencyBox (n+1) k → term r n k = 0 := by
  induction n with
  | zero => exact source_support r
  | succ n ih =>
    intro k hk
    have hm : ∀ l,¬frequencyBox (n+1) l → reducedFourierMultiplier (term r n) l = 0 := by
      intro l hl
      simp only [reducedFourierMultiplier,multiplierCLM_apply,ih l hl,map_zero]
    change r • profileMultiplication (reducedFourierMultiplier (term r n)) k = 0
    rw [profileMultiplication_support (n+1) _ hm k hk]
    exact reducedOperator_smul_zero r

theorem term_norm_le {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    ‖term r n‖ ≤ r*(3*r/2)^n :=
  (neumannTerm_norm_le _ (contraction_nonneg hr) (contrastIteration_norm_le hr) (source r) n).trans
    (mul_le_mul_of_nonneg_right (source_norm_le hr) (pow_nonneg (contraction_nonneg hr) n))

theorem weightedTerm_pointwise_bound (r : ℝ) (d : ℕ) (i : Fin 2) (n : ℕ) (k : Frequency) :
    ‖(frequencyVector k i : ℝ)^d • term r n k‖ ≤
      (3*((n : ℝ)+1))^d*‖term r n k‖ := by
  by_cases hk : frequencyBox (n+1) k
  · rw [norm_smul,Real.norm_eq_abs,abs_pow]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply pow_le_pow_left₀ (abs_nonneg _)
    simpa only [Nat.cast_add,Nat.cast_one] using frequencyBox_coordinate_bound hk i
  · rw [term_support r n k hk]
    rw [reducedOperator_smul_zero,norm_zero,mul_zero]

def weightedTerm (r : ℝ) (d : ℕ) (i : Fin 2) (n : ℕ) : ReducedCoefficients :=
  ⟨fun k => (frequencyVector k i : ℝ)^d • term r n k,by
    apply memℓp_gen
    have hs := (coefficients_summable_norm (term r n)).mul_left ((3*((n : ℝ)+1))^d)
    have hn := hs.of_nonneg_of_le (fun _ => norm_nonneg _) (weightedTerm_pointwise_bound r d i n)
    simpa only [ENNReal.toReal_one,Real.rpow_one] using hn⟩

@[simp] theorem weightedTerm_apply (r : ℝ) (d : ℕ) (i : Fin 2) (n : ℕ) (k : Frequency) :
    weightedTerm r d i n k = (frequencyVector k i : ℝ)^d • term r n k := rfl

theorem weightedTerm_norm_le {r : ℝ} (hr : 0 ≤ r) (d : ℕ) (i : Fin 2) (n : ℕ) :
    ‖weightedTerm r d i n‖ ≤ (3*((n : ℝ)+1))^d*(r*(3*r/2)^n) := by
  calc
    ‖weightedTerm r d i n‖ ≤ (3*((n : ℝ)+1))^d*‖term r n‖ := by
      rw [coefficients_norm_eq,coefficients_norm_eq]
      have hs := (coefficients_summable_norm (term r n)).mul_left ((3*((n : ℝ)+1))^d)
      exact ((coefficients_summable_norm (weightedTerm r d i n)).tsum_le_tsum
        (weightedTerm_pointwise_bound r d i n) hs).trans_eq tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (term_norm_le hr n) (by positivity)

theorem summable_polynomial_bound {r : ℝ} (hr : 0 < r) (hrlt : r < 2/3) (d : ℕ) :
    Summable (fun n : ℕ => (3*((n : ℝ)+1))^d*(r*(3*r/2)^n)) := by
  let q : ℝ := 3*r/2
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs,abs_of_pos hqpos]
    exact contraction_lt_one hrlt
  have hs := summable_pow_mul_geometric_of_norm_lt_one d hqnorm
  have hshift := (summable_nat_add_iff 1).mpr hs
  have hscaled := hshift.mul_left ((3 : ℝ)^d*r/q)
  convert hscaled using 1
  funext n
  simp only [Nat.cast_add,Nat.cast_one,pow_succ]
  dsimp [q]
  rw [mul_pow]
  field_simp [ne_of_gt hr]

theorem weightedTerm_summable {r : ℝ} (hr : 0 < r) (hrlt : r < 2/3) (d : ℕ) (i : Fin 2) :
    Summable (weightedTerm r d i) :=
  (summable_polynomial_bound hr hrlt d).of_norm_bounded (weightedTerm_norm_le hr.le d i)

def polynomialCoefficients (r : ℝ) (d : ℕ) (i : Fin 2) : ReducedCoefficients :=
  ∑' n,weightedTerm r d i n

theorem polynomialCoefficients_apply {r : ℝ} (hr : 0 < r) (hrlt : r < 2/3)
    (d : ℕ) (i : Fin 2) (k : Frequency) :
    polynomialCoefficients r d i k = (frequencyVector k i : ℝ)^d • solution r k := by
  have hs : Summable (term r) := neumannTerm_summable _ (contraction_nonneg hr.le)
    (contraction_lt_one hrlt) (contrastIteration_norm_le hr.le) (source r)
  have hev := (lp.evalCLM ℝ (fun _ : Frequency => ReducedOperator) 1 k).map_tsum
    (weightedTerm_summable hr hrlt d i)
  have hevb := (lp.evalCLM ℝ (fun _ : Frequency => ReducedOperator) 1 k).map_tsum hs
  change polynomialCoefficients r d i k = ∑' n,weightedTerm r d i n k at hev
  change solution r k = ∑' n,term r n k at hevb
  rw [hev,hevb]
  simp only [weightedTerm_apply]
  exact ((lp.evalCLM ℝ (fun _ : Frequency => ReducedOperator) 1 k).summable hs).tsum_const_smul _

/-- Every nonnegative integer moment in either frequency coordinate is summable. -/
theorem solution_frequency_moment_summable {r : ℝ} (hr : 0 < r) (hrlt : r < 2/3)
    (d : ℕ) (i : Fin 2) :
    Summable (fun k : Frequency => |(frequencyVector k i : ℝ)|^d*‖solution r k‖) := by
  simpa only [polynomialCoefficients_apply hr hrlt,norm_smul,Real.norm_eq_abs,abs_pow] using
    coefficients_summable_norm (polynomialCoefficients r d i)

def derivativeCoefficients (r : ℝ) (i : Fin 2) : ReducedCoefficients :=
  -(2*Real.pi) • polynomialCoefficients r 1 i

theorem derivativeCoefficients_apply {r : ℝ} (hr : 0 < r) (hrlt : r < 2/3)
    (i : Fin 2) (k : Frequency) :
    derivativeCoefficients r i k = -(angularFrequency k i) • solution r k := by
  change (-(2*Real.pi)) • polynomialCoefficients r 1 i k = _
  rw [polynomialCoefficients_apply hr hrlt]
  simp only [pow_one,smul_smul,angularFrequency,neg_mul]

/-- The continuous coordinate derivative field, identified below by `HasDerivAt`. -/
def responseDerivative (r : ℝ) (i : Fin 2) : C(PeriodicDomain,ReducedOperator) :=
  sineSynthesis (derivativeCoefficients r i)

theorem response_hasDerivAt_flow {r : ℝ} (hr : 0 < r) (hrlt : r < 2/3)
    (i : Fin 2) (q : PeriodicDomain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => response r (Periodic.coordinateFlow i q s))
      (responseDerivative r i (Periodic.coordinateFlow i q t)) t :=
  hasDerivAt_cosineSynthesis_flow (solution r) (derivativeCoefficients r i) i
    (derivativeCoefficients_apply hr hrlt i) q t

end HierarchicalLaminates.Contrast
