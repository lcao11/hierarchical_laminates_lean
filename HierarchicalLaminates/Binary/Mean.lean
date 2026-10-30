module

public import HierarchicalLaminates.Binary.HeightIntegral
public import HierarchicalLaminates.Fourier.Mean
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Exact binary phase fraction

The sampled cosine widths are integrated against the normalized product
Haar measure of the periodic field space.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Binary

open MeasureTheory Set HierarchicalLaminates.Periodic HierarchicalLaminates.Fourier

local notation "μcircle" => AddCircle.haarAddCircle (T := (1 : ℝ))

theorem binaryIndicator_integrable (N : ℕ) :
    Integrable (binaryIndicator N) domainMeasure := by
  apply Integrable.of_bound (binaryIndicator_measurable N).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun q => by
    rw [Real.norm_eq_abs, abs_of_nonneg (binaryIndicator_mem N q).1]
    exact (binaryIndicator_mem N q).2

theorem binaryIndicator_product_integrable (N : ℕ) :
    Integrable (fun p : UnitAddCircle × UnitAddCircle => binaryIndicator N ![p.1, p.2])
      ((μcircle).prod μcircle) := by
  refine Integrable.of_bound ?_ 1 ?_
  · apply Measurable.aestronglyMeasurable
    apply (binaryIndicator_measurable N).comp
    apply Measurable.of_eval
    intro i
    fin_cases i
    · exact measurable_fst
    · exact measurable_snd
  · exact Filter.Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs, abs_of_nonneg (binaryIndicator_mem N _).1]
      exact (binaryIndicator_mem N _).2

theorem binaryIndicator_mean_as_iterated (N : ℕ) :
    (∫ q, binaryIndicator N q ∂domainMeasure) =
      ∫ x : UnitAddCircle, ∫ y : UnitAddCircle, binaryIndicator N ![x, y]
        ∂μcircle ∂μcircle := by
  have h := (measurePreserving_finTwoArrow μcircle).integral_comp'
    (fun p : UnitAddCircle × UnitAddCircle => binaryIndicator N ![p.1, p.2])
  have hq : (fun q : Domain => binaryIndicator N
      ![(MeasurableEquiv.finTwoArrow q).1, (MeasurableEquiv.finTwoArrow q).2]) =
      binaryIndicator N := by
    funext q
    congr 1
    ext i
    fin_cases i <;> rfl
  rw [hq] at h
  change (∫ q, binaryIndicator N q ∂domainMeasure) = _ at h
  rw [h]
  exact integral_prod _ (binaryIndicator_product_integrable N)

/-- Reduces exact two-dimensional phase volume to the finite sampled widths. -/
theorem binaryIndicator_mean_as_sampled {N : ℕ} (hN : 0 < N) :
    (∫ q, binaryIndicator N q ∂domainMeasure) =
      ∫ x : UnitAddCircle, ∑ k ∈ Finset.range N, stripFraction N k x / N ∂μcircle := by
  rw [binaryIndicator_mean_as_iterated]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => binaryIndicator_circle_height_integral hN x

theorem horizontalCharacter_integrable (k : ℤ × ℤ) (y : UnitAddCircle) :
    Integrable (fun x : UnitAddCircle => phaseCharacter k ![x, y]) μcircle := by
  refine Integrable.of_bound ?_ 1 ?_
  · have hc : Continuous (fun x : UnitAddCircle => phaseCharacter k ![x, y]) := by
      apply (phaseCharacter k).continuous.comp
      apply continuous_pi
      intro i
      fin_cases i
      · exact continuous_id
      · exact continuous_const
    exact hc.measurable.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => phaseCharacter_norm_le k _

theorem integral_horizontalCharacter (k : ℤ × ℤ) (y : UnitAddCircle) :
    (∫ x : UnitAddCircle, phaseCharacter k ![x, y] ∂μcircle) =
      (if k.1 = 0 then (1 : ℂ) else 0) * fourier k.2 y := by
  simp only [phaseCharacter, UnitAddTorus.mFourier, frequencyVector, Fin.prod_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.prod_univ_zero, mul_one]
  change (∫ x : UnitAddCircle, fourier k.1 x * fourier k.2 y ∂μcircle) = _
  rw [integral_mul_const, integral_unitFourier]

theorem horizontalCosine_integrable (k : ℤ × ℤ) (y : UnitAddCircle) :
    Integrable (fun x : UnitAddCircle => cosineKernel k ![x, y]) μcircle := by
  exact Complex.reCLM.integrable_comp (horizontalCharacter_integrable k y)

theorem integral_horizontalCosine (k : ℤ × ℤ) (y : UnitAddCircle) :
    (∫ x : UnitAddCircle, cosineKernel k ![x, y] ∂μcircle) =
      if k.1 = 0 then (fourier k.2 y).re else 0 := by
  change (∫ x : UnitAddCircle, (phaseCharacter k ![x, y]).re ∂μcircle) = _
  have h := Complex.reCLM.integral_comp_comm (horizontalCharacter_integrable k y)
  simp only [Complex.reCLM_apply] at h
  rw [h, integral_horizontalCharacter]
  by_cases hk : k.1 = 0 <;> simp [hk]

/-- Only the purely vertical cosine survives horizontal averaging. -/
theorem stripFraction_horizontal_integral (N k : ℕ) :
    (∫ x : UnitAddCircle, stripFraction N k x ∂μcircle) =
      (1 / 2 : ℝ) + (1 / 6 : ℝ) *
        (fourier 1 (((k : ℝ) / N : ℝ) : UnitAddCircle)).re := by
  unfold stripFraction
  simp only [cosineProfile, ContinuousMap.add_apply, ContinuousMap.smul_apply,
    ContinuousMap.one_apply, smul_eq_mul]
  simp only [mul_one]
  let y : UnitAddCircle := (((k : ℝ) / N : ℝ) : UnitAddCircle)
  have ha := horizontalCosine_integrable (1, 0) y
  have hb := horizontalCosine_integrable (0, 1) y
  have hc := horizontalCosine_integrable (1, 3) y
  have hab : Integrable (fun x : UnitAddCircle => cosineKernel (1, 0) ![x, y] +
      cosineKernel (0, 1) ![x, y]) μcircle := ha.add hb
  have hsum : Integrable (fun x : UnitAddCircle => cosineKernel (1, 0) ![x, y] +
      cosineKernel (0, 1) ![x, y] + cosineKernel (1, 3) ![x, y]) μcircle :=
    (ha.add hb).add hc
  change (∫ x : UnitAddCircle, (1 / 2 : ℝ) + (1 / 6 : ℝ) *
    (cosineKernel (1, 0) ![x, y] + cosineKernel (0, 1) ![x, y] +
      cosineKernel (1, 3) ![x, y]) ∂μcircle) = _
  rw [integral_add (integrable_const _) (hsum.const_mul _), integral_const_mul,
    integral_add hab hc, integral_add ha hb]
  simp [integral_horizontalCosine, y]

theorem stripFraction_integrable (N k : ℕ) :
    Integrable (stripFraction N k) μcircle := by
  refine Integrable.of_bound ?_ 1 ?_
  · have hc : Continuous (stripFraction N k) := by
      apply cosineProfile.continuous.comp
      apply continuous_pi
      intro i
      fin_cases i
      · exact continuous_id
      · exact continuous_const
    exact hc.measurable.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by
      change ‖cosineProfile ![x, (((k : ℝ) / N : ℝ) : UnitAddCircle)]‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (cosineProfile_nonneg _)]
      exact cosineProfile_le_one _

/-- The phase fraction as a finite sum of sampled widths. -/
theorem binaryIndicator_mean_finite {N : ℕ} (hN : 0 < N) :
    (∫ q, binaryIndicator N q ∂domainMeasure) =
      ∑ k ∈ Finset.range N, ((1 / 2 : ℝ) + (1 / 6 : ℝ) *
        (fourier 1 (((k : ℝ) / N : ℝ) : UnitAddCircle)).re) / N := by
  rw [binaryIndicator_mean_as_sampled hN,
    integral_finsetSum _ (fun k hk => (stripFraction_integrable N k).div_const _)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_div, stripFraction_horizontal_integral]

theorem fourier_sample_even_pair {M : ℕ} (hM : 0 < M) (k : ℕ) :
    fourier 1 (((((M + k : ℕ) : ℝ) / (M + M : ℕ) : ℝ)) : UnitAddCircle) =
      -fourier 1 ((((k : ℝ) / (M + M : ℕ) : ℝ)) : UnitAddCircle) := by
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have hx : (((M + k : ℕ) : ℝ) / (M + M : ℕ) : ℝ) =
      (k : ℝ) / (M + M : ℕ) + 1 / 2 := by
    norm_num only [Nat.cast_add]
    field_simp
    ring
  rw [hx, AddCircle.coe_add]
  have h := fourier_add_half_inv_index (T := (1 : ℝ)) (n := 1)
    (by norm_num) (by norm_num) ((((k : ℝ) / (M + M : ℕ) : ℝ)) : UnitAddCircle)
  simpa only [Int.cast_one, div_one] using h

/-- Pairing opposite sample points proves exact cancellation for every even count. -/
theorem fourier_sample_even_sum {M : ℕ} (hM : 0 < M) :
    (∑ k ∈ Finset.range (M + M),
      (fourier 1 ((((k : ℝ) / (M + M : ℕ) : ℝ)) : UnitAddCircle)).re) = 0 := by
  rw [Finset.sum_range_add]
  have hpair : (∑ k ∈ Finset.range M,
      (fourier 1 (((((M + k : ℕ) : ℝ) / (M + M : ℕ) : ℝ)) : UnitAddCircle)).re) =
      -(∑ k ∈ Finset.range M,
        (fourier 1 ((((k : ℝ) / (M + M : ℕ) : ℝ)) : UnitAddCircle)).re) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [fourier_sample_even_pair hM k, Complex.neg_re]
  rw [hpair, add_neg_cancel]

/-- Every positive even strip count gives phase volume exactly 1/2. -/
theorem binaryIndicator_mean_half_even {M : ℕ} (hM : 0 < M) :
    (∫ q, binaryIndicator (M + M) q ∂domainMeasure) = (1 / 2 : ℝ) := by
  have hN : 0 < M + M := Nat.add_pos_left hM M
  have hNr : ((M + M : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  rw [binaryIndicator_mean_finite hN]
  simp_rw [add_div, mul_div_assoc]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← Finset.sum_div, fourier_sample_even_sum hM]
  field_simp
  ring

end HierarchicalLaminates.Binary
