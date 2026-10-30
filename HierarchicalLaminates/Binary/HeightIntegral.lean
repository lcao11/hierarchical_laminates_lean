module

public import HierarchicalLaminates.Binary.Geometry
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Exact integration of a binary stripe

Integrating the strict-cutoff indicator gives the strip width. Endpoint
conventions agree up to a null set.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Binary

open MeasureTheory Set HierarchicalLaminates.Periodic HierarchicalLaminates.Fourier

/-- The fraction of one strip occupied by the material is exactly its width. -/
theorem stripeIndicator_integral {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ τ in Ico (0 : ℝ) 1, stripeIndicator τ t) = t := by
  have hs : (Iio t ∩ Ico (0 : ℝ) 1) = Ico 0 t := by
    ext τ
    simp only [mem_inter_iff, mem_Iio, mem_Ico]
    constructor
    · rintro ⟨hτt, hτ0, hτ1⟩
      exact ⟨hτ0, hτt⟩
    · rintro ⟨hτ0, hτt⟩
      exact ⟨hτt, hτ0, hτt.trans_le ht.2⟩
  have hf : (fun τ => stripeIndicator τ t) = (Iio t).indicator (fun _ : ℝ => (1 : ℝ)) := by
    funext τ
    simp [stripeIndicator, Set.indicator]
  rw [hf, integral_indicator_const (1 : ℝ) measurableSet_Iio]
  simp only [smul_eq_mul, mul_one]
  rw [measureReal_restrict_apply measurableSet_Iio, hs]
  simp [Measure.real, Real.volume_Ico, ht.1]

/-- The same exact fraction in interval-integral form. -/
theorem stripeIndicator_intervalIntegral {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ τ in (0 : ℝ)..1, stripeIndicator τ t) = t := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [← integral_Ico_eq_integral_Ioc]
  exact stripeIndicator_integral ht

/-- The sampled height in strip `k`, expressed in the global vertical coordinate. -/
def stripFraction (N k : ℕ) (x : UnitAddCircle) : ℝ :=
  cosineProfile ![x, (((k : ℝ) / N : ℝ) : UnitAddCircle)]

/-- A point expressed in local coordinates of strip `k`. -/
def pointInStrip (N k : ℕ) (x : UnitAddCircle) (τ : ℝ) : Domain :=
  ![x, ((((k : ℝ) + τ) / N : ℝ) : UnitAddCircle)]

theorem pointInStrip_height_mem {N k : ℕ} (hN : 0 < N) (hk : k < N)
    {τ : ℝ} (hτ : τ ∈ Ico (0 : ℝ) 1) :
    ((k : ℝ) + τ) / N ∈ Ico (0 : ℝ) 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hkN : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
  constructor
  · exact div_nonneg (add_nonneg (Nat.cast_nonneg k) hτ.1) (le_of_lt hNr)
  · apply (div_lt_one hNr).mpr
    linarith [hτ.2]

theorem pointInStrip_representative {N k : ℕ} (hN : 0 < N) (hk : k < N)
    (x : UnitAddCircle) {τ : ℝ} (hτ : τ ∈ Ico (0 : ℝ) 1) :
    coordinateRepresentative 1 (pointInStrip N k x τ) = ((k : ℝ) + τ) / N := by
  change (AddCircle.equivIco 1 0 ((((k : ℝ) + τ) / N : ℝ) : UnitAddCircle)).1 = _
  exact AddCircle.equivIco_coe_of_mem (by simpa using pointInStrip_height_mem hN hk hτ)

theorem stripIndex_pointInStrip {N k : ℕ} (hN : 0 < N) (hk : k < N)
    (x : UnitAddCircle) {τ : ℝ} (hτ : τ ∈ Ico (0 : ℝ) 1) :
    stripIndex N (pointInStrip N k x τ) = (k : ℤ) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  unfold stripIndex
  rw [pointInStrip_representative hN hk x hτ, mul_div_cancel₀ _ hNr]
  apply Int.floor_eq_iff.mpr
  simp only [Int.cast_natCast]
  constructor <;> linarith [hτ.1, hτ.2]

theorem stripCoordinate_pointInStrip {N k : ℕ} (hN : 0 < N) (hk : k < N)
    (x : UnitAddCircle) {τ : ℝ} (hτ : τ ∈ Ico (0 : ℝ) 1) :
    stripCoordinate N (pointInStrip N k x τ) = τ := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  unfold stripCoordinate
  rw [pointInStrip_representative hN hk x hτ, stripIndex_pointInStrip hN hk x hτ]
  norm_num only [Int.cast_natCast]
  field_simp
  ring

/-- Restriction of the torus indicator to one strip gives its local cutoff. -/
theorem binaryIndicator_pointInStrip {N k : ℕ} (hN : 0 < N) (hk : k < N)
    (x : UnitAddCircle) {τ : ℝ} (hτ : τ ∈ Ico (0 : ℝ) 1) :
    binaryIndicator N (pointInStrip N k x τ) = stripeIndicator τ (stripFraction N k x) := by
  unfold binaryIndicator
  rw [stripCoordinate_pointInStrip hN hk x hτ]
  congr 1
  unfold sampledFraction sampledPoint stripFraction
  rw [stripIndex_pointInStrip hN hk x hτ]
  rfl

/-- The strip integral of the torus indicator in local coordinates. -/
theorem binaryIndicator_localIntegral {N k : ℕ} (hN : 0 < N) (hk : k < N)
    (x : UnitAddCircle) :
    (∫ τ in (0 : ℝ)..1, binaryIndicator N (pointInStrip N k x τ)) =
      stripFraction N k x := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [← integral_Ico_eq_integral_Ioc]
  calc
    (∫ τ in Ico (0 : ℝ) 1, binaryIndicator N (pointInStrip N k x τ)) =
        ∫ τ in Ico (0 : ℝ) 1, stripeIndicator τ (stripFraction N k x) := by
      apply setIntegral_congr_fun measurableSet_Ico
      intro τ hτ
      exact binaryIndicator_pointInStrip hN hk x hτ
    _ = stripFraction N k x := stripeIndicator_integral
      ⟨cosineProfile_nonneg _, cosineProfile_le_one _⟩

/-- Exact strip measure in the vertical coordinate. -/
theorem binaryIndicator_stripIntegral {N k : ℕ} (hN : 0 < N) (hk : k < N)
    (x : UnitAddCircle) :
    (∫ y in (k : ℝ) / N..((k : ℝ) + 1) / N,
      binaryIndicator N ![x, (y : UnitAddCircle)]) = stripFraction N k x / N := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have h := binaryIndicator_localIntegral hN hk x
  change (∫ τ in (0 : ℝ)..1,
      binaryIndicator N ![x, ((((k : ℝ) + τ) / N : ℝ) : UnitAddCircle)]) = _ at h
  rw [intervalIntegral.integral_comp_add_left
    (fun y : ℝ => binaryIndicator N ![x, ((y / N : ℝ) : UnitAddCircle)]) (k : ℝ),
    intervalIntegral.integral_comp_div
      (fun y : ℝ => binaryIndicator N ![x, (y : UnitAddCircle)]) hNr] at h
  simp only [add_zero, smul_eq_mul] at h
  exact (eq_div_iff hNr).mpr (by simpa only [mul_comm] using h)

theorem binaryIndicator_height_measurable (N : ℕ) (x : UnitAddCircle) :
    Measurable (fun y : ℝ => binaryIndicator N ![x, (y : UnitAddCircle)]) := by
  apply (binaryIndicator_measurable N).comp
  apply Measurable.of_eval
  intro i
  fin_cases i
  · exact measurable_const
  · exact AddCircle.measurable_mk'

theorem binaryIndicator_height_intervalIntegrable (N : ℕ) (x : UnitAddCircle)
    (a b : ℝ) :
    IntervalIntegrable (fun y : ℝ => binaryIndicator N ![x, (y : UnitAddCircle)])
      volume a b := by
  apply intervalIntegrable_iff.mpr
  apply IntegrableOn.of_bound (by simp only [Real.volume_uIoc]; exact ENNReal.ofReal_lt_top)
    (binaryIndicator_height_measurable N x).aestronglyMeasurable.restrict 1
  exact Filter.Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (binaryIndicator_mem N _).1]
    exact (binaryIndicator_mem N _).2

/-- The exact vertical integral is the arithmetic mean of the sampled widths. -/
theorem binaryIndicator_height_integral {N : ℕ} (hN : 0 < N) (x : UnitAddCircle) :
    (∫ y in (0 : ℝ)..1, binaryIndicator N ![x, (y : UnitAddCircle)]) =
      ∑ k ∈ Finset.range N, stripFraction N k x / N := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have h := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => (k : ℝ) / N)
    (n := N) (f := fun y : ℝ => binaryIndicator N ![x, (y : UnitAddCircle)])
    (fun k hk => binaryIndicator_height_intervalIntegrable N x _ _)
  simp only [Nat.cast_zero, zero_div, div_self hNr] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro k hk
  simpa only [Nat.cast_add, Nat.cast_one] using
    binaryIndicator_stripIntegral hN (Finset.mem_range.mp hk) x

/-- The torus vertical average uses the same normalized measure as the L² model. -/
theorem binaryIndicator_circle_height_integral {N : ℕ} (hN : 0 < N)
    (x : UnitAddCircle) :
    (∫ y : UnitAddCircle, binaryIndicator N ![x, y]
      ∂AddCircle.haarAddCircle (T := (1 : ℝ))) =
      ∑ k ∈ Finset.range N, stripFraction N k x / N := by
  have h := UnitAddCircle.intervalIntegral_preimage (0 : ℝ)
    (fun y : UnitAddCircle => binaryIndicator N ![x, y])
  simp only [zero_add] at h
  rw [AddCircle.volume_eq_smul_haarAddCircle] at h
  simpa only [ENNReal.ofReal_one, one_smul] using
    h.symm.trans (binaryIndicator_height_integral hN x)

end HierarchicalLaminates.Binary
