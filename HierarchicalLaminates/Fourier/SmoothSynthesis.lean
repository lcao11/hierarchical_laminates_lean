module

public import HierarchicalLaminates.Fourier.WeightedRegularity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Joint smoothness from summable frequency moments

For coefficients in a real Banach space, absolute summability of every pure
coordinate frequency moment implies joint C∞ regularity of sine and cosine
synthesis. Smoothness is expressed on the periodic lift from the unit torus
to `ℝ²`.

Differentiation replaces each coefficient by a continuous linear map whose
norm is controlled by the frequency. Higher pure moments also control mixed
frequency products, so the differentiated coefficients satisfy the same
moment condition. Induction in the Banach-valued derivative space gives full
Fréchet smoothness, including all mixed derivatives.
-/

@[expose] public section
noncomputable section

namespace HierarchicalLaminates.Fourier

open HierarchicalLaminates
open scoped ContDiff ENNReal

/-- The real coordinate space covering the two-dimensional unit torus. -/
abbrev LiftDomain := Fin 2 → ℝ

/-- Pull a torus function back along the coordinatewise quotient map `ℝ² → 𝕋²`. -/
def torusLift {E : Type*} [TopologicalSpace E] (f : C(PeriodicDomain, E)) : LiftDomain → E :=
  fun x => f (fun i => (x i : UnitAddCircle))

theorem torusLift_continuous {E : Type*} [TopologicalSpace E] (f : C(PeriodicDomain, E)) :
    Continuous (torusLift f) := by
  apply f.continuous.comp
  apply continuous_pi
  intro i
  exact (AddCircle.continuous_mk' (p := (1 : ℝ))).comp (continuous_apply i)

/-- The angular phase `x ↦ 2π (k₁ x₁ + k₂ x₂)` as a continuous linear map. -/
def frequencyLinear (k : Frequency) : LiftDomain →L[ℝ] ℝ :=
  (2 * Real.pi * (k.1 : ℝ)) • ContinuousLinearMap.proj 0 +
    (2 * Real.pi * (k.2 : ℝ)) • ContinuousLinearMap.proj 1

@[simp] theorem frequencyLinear_apply (k : Frequency) (x : LiftDomain) :
    frequencyLinear k x = 2 * Real.pi * ((k.1 : ℝ)*x 0+(k.2 : ℝ)*x 1) := by
  simp only [frequencyLinear, _root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  ring

theorem frequencyLinear_norm_le (k : Frequency) :
    ‖frequencyLinear k‖ ≤ 2 * Real.pi * (|(k.1 : ℝ)|+|(k.2 : ℝ)|) := by
  have hproj (i : Fin 2) : ‖(ContinuousLinearMap.proj i : LiftDomain →L[ℝ] ℝ)‖ ≤ 1 := by
    apply (ContinuousLinearMap.proj i : LiftDomain →L[ℝ] ℝ).opNorm_le_bound zero_le_one
    intro x
    rw [ContinuousLinearMap.proj_apply, one_mul]
    exact norm_le_pi_norm x i
  calc
    ‖frequencyLinear k‖ ≤
        ‖(2 * Real.pi * (k.1 : ℝ)) • (ContinuousLinearMap.proj 0 : LiftDomain →L[ℝ] ℝ)‖+
        ‖(2 * Real.pi * (k.2 : ℝ)) • (ContinuousLinearMap.proj 1 : LiftDomain →L[ℝ] ℝ)‖ := norm_add_le _ _
    _ ≤ |2 * Real.pi * (k.1 : ℝ)|+|2 * Real.pi * (k.2 : ℝ)| := by
      simp only [norm_smul, Real.norm_eq_abs]
      exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) (hproj 0))
        (mul_le_of_le_one_right (abs_nonneg _) (hproj 1))
    _ = _ := by simp only [abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ)<2)]; ring

theorem cosineKernel_lift (k : Frequency) :
    torusLift (cosineKernel k) = fun x => Real.cos (frequencyLinear k x) := by
  funext x
  change (phaseCharacter k (fun i => (x i : UnitAddCircle))).re = _
  rw [phaseCharacter_lift]
  have he : 2*(Real.pi : ℂ)*Complex.I*((k.1 : ℂ)*(x 0 : ℂ)+(k.2 : ℂ)*(x 1 : ℂ)) =
      (frequencyLinear k x : ℂ)*Complex.I := by rw [frequencyLinear_apply]; push_cast; ring
  rw [he, Complex.exp_ofReal_mul_I_re]

theorem sineKernel_lift (k : Frequency) :
    torusLift (sineKernel k) = fun x => Real.sin (frequencyLinear k x) := by
  funext x
  change (phaseCharacter k (fun i => (x i : UnitAddCircle))).im = _
  rw [phaseCharacter_lift]
  have he : 2*(Real.pi : ℂ)*Complex.I*((k.1 : ℂ)*(x 0 : ℂ)+(k.2 : ℂ)*(x 1 : ℂ)) =
      (frequencyLinear k x : ℂ)*Complex.I := by rw [frequencyLinear_apply]; push_cast; ring
  rw [he, Complex.exp_ofReal_mul_I_im]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Every pure coordinate frequency moment is absolutely summable, including
degree zero. Higher degrees also bound the mixed products needed for joint derivatives. -/
def HasFrequencyMoments (f : Coefficients Frequency E) : Prop :=
  ∀ (d : ℕ) (i : Fin 2),
    Summable (fun k => |(frequencyVector k i : ℝ)| ^ d * ‖f k‖)

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- A uniform coefficient norm bound transfers every frequency moment. -/
theorem HasFrequencyMoments.of_norm_le
    {F : Type*} [NormedAddCommGroup F]
    {f : Coefficients Frequency E} {g : Coefficients Frequency F}
    (hf : HasFrequencyMoments f) (C : ℝ) (_hC : 0 ≤ C)
    (hg : ∀ k, ‖g k‖ ≤ C*‖f k‖) : HasFrequencyMoments g := by
  intro d i
  have hs : Summable (fun k => |(frequencyVector k i : ℝ)|^d*(C*‖f k‖)) := by
    convert (hf d i).mul_left C using 1
    funext k
    ring
  exact hs.of_nonneg_of_le (fun _ => by positivity)
    (fun k => mul_le_mul_of_nonneg_left (hg k) (by positivity))

omit [CompleteSpace E] in
theorem HasFrequencyMoments.smul {f : Coefficients Frequency E}
    (hf : HasFrequencyMoments f) (r : ℝ) : HasFrequencyMoments (r • f) := by
  apply hf.of_norm_le |r| (abs_nonneg r)
  intro k
  change ‖r • f k‖ ≤ |r| * ‖f k‖
  rw [norm_smul, Real.norm_eq_abs]

/-- The bounded reduced Fourier multiplier preserves all frequency moments. -/
theorem reducedFourierMultiplier_moments {f : ReducedCoefficients}
    (hf : HasFrequencyMoments f) : HasFrequencyMoments (reducedFourierMultiplier f) := by
  apply hf.of_norm_le (3/2) (by norm_num)
  intro k
  exact coefficientSymbolAction_norm_le k (f k)

private theorem pow_mul_le_sum (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (d : ℕ) :
    a^d*b ≤ a^(d+1)+b^(d+1) := by
  by_cases hab : a ≤ b
  · have h := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hab d) hb
    rw [← pow_succ] at h
    exact h.trans (le_add_of_nonneg_left (pow_nonneg ha _))
  · have h := mul_le_mul_of_nonneg_left (le_of_not_ge hab) (pow_nonneg ha d)
    rw [← pow_succ] at h
    exact h.trans (le_add_of_nonneg_right (pow_nonneg hb _))

private def derivativeBound (d : ℕ) (i : Fin 2) (f : Coefficients Frequency E) (k : Frequency) : ℝ :=
  2*Real.pi *
    (2*|(frequencyVector k i : ℝ)|^(d+1)+|(k.1 : ℝ)|^(d+1)+|(k.2 : ℝ)|^(d+1))*‖f k‖

omit [NormedSpace ℝ E] [CompleteSpace E] in
private theorem derivativeBound_summable (f : Coefficients Frequency E) (hf : HasFrequencyMoments f)
    (d : ℕ) (i : Fin 2) : Summable (derivativeBound d i f) := by
  have hs := (((hf (d+1) i).mul_left 2).add (hf (d+1) 0)).add (hf (d+1) 1)
  convert hs.mul_left (2*Real.pi) using 1
  funext k
  simp only [derivativeBound, frequencyVector, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

omit [CompleteSpace E] in
private theorem frequencyDerivative_bound (f : Coefficients Frequency E) (d : ℕ) (i : Fin 2)
    (k : Frequency) :
    |(frequencyVector k i : ℝ)|^d*‖(frequencyLinear k).smulRight (f k)‖ ≤ derivativeBound d i f k := by
  rw [ContinuousLinearMap.norm_smulRight_apply]
  have hp := mul_le_mul_of_nonneg_right (frequencyLinear_norm_le k) (norm_nonneg (f k))
  have hw := mul_le_mul_of_nonneg_left hp (pow_nonneg (abs_nonneg (frequencyVector k i : ℝ)) d)
  have h0 := pow_mul_le_sum |(frequencyVector k i : ℝ)| |(k.1 : ℝ)| (abs_nonneg _) (abs_nonneg _) d
  have h1 := pow_mul_le_sum |(frequencyVector k i : ℝ)| |(k.2 : ℝ)| (abs_nonneg _) (abs_nonneg _) d
  have hsum := add_le_add h0 h1
  have hscaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 2*Real.pi)) (norm_nonneg (f k))
  exact hw.trans (by dsimp [derivativeBound]; nlinarith only [hscaled])

/-- Coefficients of the Fréchet derivative, taking values in continuous linear
maps from the real lift domain. The moment hypothesis ensures absolute summability. -/
def frequencyDerivativeCoefficients (f : Coefficients Frequency E) (hf : HasFrequencyMoments f) :
    Coefficients Frequency (LiftDomain →L[ℝ] E) :=
  ⟨fun k => (frequencyLinear k).smulRight (f k), by
    apply memℓp_gen
    have h := (derivativeBound_summable f hf 0 0).of_nonneg_of_le
      (fun k => norm_nonneg ((frequencyLinear k).smulRight (f k)))
      (fun k => by simpa only [pow_zero, one_mul] using frequencyDerivative_bound f 0 0 k)
    simpa only [ENNReal.toReal_one, Real.rpow_one] using h⟩

omit [CompleteSpace E] in
@[simp] theorem frequencyDerivativeCoefficients_apply
    (f : Coefficients Frequency E) (hf : HasFrequencyMoments f) (k : Frequency) :
    frequencyDerivativeCoefficients f hf k = (frequencyLinear k).smulRight (f k) := rfl

omit [CompleteSpace E] in
/-- Derivative coefficients retain every moment, allowing repeated differentiation. -/
theorem frequencyDerivativeCoefficients_moments (f : Coefficients Frequency E)
    (hf : HasFrequencyMoments f) : HasFrequencyMoments (frequencyDerivativeCoefficients f hf) := by
  intro d i
  exact (derivativeBound_summable f hf d i).of_nonneg_of_le
    (fun _ => mul_nonneg (pow_nonneg (abs_nonneg _) _) (norm_nonneg _))
    (frequencyDerivative_bound f d i)

omit [CompleteSpace E] in
theorem hasFDerivAt_cosineKernel_term (k : Frequency) (e : E) (x : LiftDomain) :
    HasFDerivAt (fun y => torusLift (cosineKernel k) y • e)
      (-(torusLift (sineKernel k) x) • (frequencyLinear k).smulRight e) x := by
  rw [cosineKernel_lift, sineKernel_lift]
  convert ((frequencyLinear k).hasFDerivAt.cos).smul_const e using 1
  ext v
  simp only [ContinuousLinearMap.smulRight_apply, _root_.smul_apply, smul_smul, smul_eq_mul]

omit [CompleteSpace E] in
theorem hasFDerivAt_sineKernel_term (k : Frequency) (e : E) (x : LiftDomain) :
    HasFDerivAt (fun y => torusLift (sineKernel k) y • e)
      (torusLift (cosineKernel k) x • (frequencyLinear k).smulRight e) x := by
  rw [cosineKernel_lift, sineKernel_lift]
  convert ((frequencyLinear k).hasFDerivAt.sin).smul_const e using 1
  ext v
  simp only [ContinuousLinearMap.smulRight_apply, _root_.smul_apply, smul_smul, smul_eq_mul]

theorem torusLift_cosineSynthesis (f : Coefficients Frequency E) :
    torusLift (cosineSynthesis f) = fun x => ∑' k, torusLift (cosineKernel k) x • f k := by
  funext x
  exact continuousSynthesis_apply cosineKernel cosineKernel_norm_le f _

theorem torusLift_sineSynthesis (f : Coefficients Frequency E) :
    torusLift (sineSynthesis f) = fun x => ∑' k, torusLift (sineKernel k) x • f k := by
  funext x
  exact continuousSynthesis_apply sineKernel sineKernel_norm_le f _

/-- Differentiate the cosine sum termwise; the derivative is the negative
sine synthesis of the continuous-linear-map coefficients. -/
theorem hasFDerivAt_cosineSynthesis_lift (f : Coefficients Frequency E)
    (hf : HasFrequencyMoments f) (x : LiftDomain) :
    HasFDerivAt (torusLift (cosineSynthesis f))
      (-torusLift (sineSynthesis (frequencyDerivativeCoefficients f hf)) x) x := by
  let df := frequencyDerivativeCoefficients f hf
  have ht (k : Frequency) (y : LiftDomain) :
      HasFDerivAt (fun z => torusLift (cosineKernel k) z • f k)
        ((-(torusLift (sineKernel k) y)) • df k) y :=
    hasFDerivAt_cosineKernel_term k (f k) y
  have hb (k : Frequency) (y : LiftDomain) :
      ‖(-(torusLift (sineKernel k) y)) • df k‖ ≤ ‖df k‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg]
    exact mul_le_of_le_one_left (norm_nonneg _) (sineKernel_abs_le k _)
  have hs : Summable (fun k : Frequency => torusLift (cosineKernel k) (0 : LiftDomain) • f k) :=
    pointwiseSynthesis_summable cosineKernel cosineKernel_norm_le f _
  have h := hasFDerivAt_tsum (coefficients_summable_norm df) ht hb hs x
  rw [torusLift_cosineSynthesis, torusLift_sineSynthesis]
  have hd : (∑' k, (-(torusLift (sineKernel k) x)) • df k) =
      -(∑' k, torusLift (sineKernel k) x • df k) := by
    exact (tsum_congr (fun k => neg_smul (torusLift (sineKernel k) x) (df k))).trans tsum_neg
  erw [hd] at h
  exact h

/-- Differentiate the sine sum termwise to obtain cosine synthesis of the
continuous-linear-map coefficients. -/
theorem hasFDerivAt_sineSynthesis_lift (f : Coefficients Frequency E)
    (hf : HasFrequencyMoments f) (x : LiftDomain) :
    HasFDerivAt (torusLift (sineSynthesis f))
      (torusLift (cosineSynthesis (frequencyDerivativeCoefficients f hf)) x) x := by
  let df := frequencyDerivativeCoefficients f hf
  have ht (k : Frequency) (y : LiftDomain) :
      HasFDerivAt (fun z => torusLift (sineKernel k) z • f k)
        (torusLift (cosineKernel k) y • df k) y :=
    hasFDerivAt_sineKernel_term k (f k) y
  have hb (k : Frequency) (y : LiftDomain) :
      ‖torusLift (cosineKernel k) y • df k‖ ≤ ‖df k‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (cosineKernel_abs_le k _)
  have hs : Summable (fun k : Frequency => torusLift (sineKernel k) (0 : LiftDomain) • f k) :=
    pointwiseSynthesis_summable sineKernel sineKernel_norm_le f _
  have h := hasFDerivAt_tsum (coefficients_summable_norm df) ht hb hs x
  rw [torusLift_sineSynthesis, torusLift_cosineSynthesis]
  exact h

/-- Sine and cosine synthesis have every finite order of joint Fréchet regularity. -/
theorem contDiff_synthesis_of_moments (n : ℕ) (f : Coefficients Frequency E)
    (hf : HasFrequencyMoments f) :
    ContDiff ℝ n (torusLift (cosineSynthesis f)) ∧
      ContDiff ℝ n (torusLift (sineSynthesis f)) := by
  induction n generalizing E with
  | zero =>
      exact ⟨contDiff_zero.mpr (torusLift_continuous _),
        contDiff_zero.mpr (torusLift_continuous _)⟩
  | succ n ih =>
      have hd := ih (frequencyDerivativeCoefficients f hf) (frequencyDerivativeCoefficients_moments f hf)
      constructor
      · rw [show ((n+1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞)+1 by simp,
          contDiff_succ_iff_hasFDerivAt]
        exact ⟨fun x => -torusLift (sineSynthesis (frequencyDerivativeCoefficients f hf)) x,
          hd.2.neg, hasFDerivAt_cosineSynthesis_lift f hf⟩
      · rw [show ((n+1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞)+1 by simp,
          contDiff_succ_iff_hasFDerivAt]
        exact ⟨torusLift (cosineSynthesis (frequencyDerivativeCoefficients f hf)),
          hd.1, hasFDerivAt_sineSynthesis_lift f hf⟩

/-- All polynomial coordinate moments give full joint C∞ regularity, including mixed derivatives. -/
theorem cosineSynthesis_smooth (f : Coefficients Frequency E) (hf : HasFrequencyMoments f) :
    ContDiff ℝ ∞ (torusLift (cosineSynthesis f)) :=
  contDiff_infty.mpr (fun n => (contDiff_synthesis_of_moments n f hf).1)

/-- The periodic real lift of sine synthesis is jointly C∞. -/
theorem sineSynthesis_smooth (f : Coefficients Frequency E) (hf : HasFrequencyMoments f) :
    ContDiff ℝ ∞ (torusLift (sineSynthesis f)) :=
  contDiff_infty.mpr (fun n => (contDiff_synthesis_of_moments n f hf).2)

/-- The fixed-contrast reduced response has a jointly smooth periodic real lift. -/
theorem reducedResponse_smooth : ContDiff ℝ ∞ (torusLift reducedResponse) :=
  cosineSynthesis_smooth rhoSolution rhoSolution_frequency_moment_summable

end HierarchicalLaminates.Fourier
