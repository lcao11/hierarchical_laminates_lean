module

public import HierarchicalLaminates.Fourier.Characters
public import HierarchicalLaminates.Fourier.ProfileOperators
public import HierarchicalLaminates.Fourier.Synthesis
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module

/-!
# The cosine profile and its seven-frequency multiplication identity

All seven Fourier coefficients enter the coefficient action, whose synthesis
is pointwise multiplication by the prescribed profile.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Fourier

def cosineProfile : C(PeriodicDomain, ℝ) :=
  (1 / 2 : ℝ) • (1 : C(PeriodicDomain, ℝ)) +
    (1 / 6 : ℝ) • (cosineKernel (1, 0) + cosineKernel (0, 1) + cosineKernel (1, 3))

theorem cosineProfile_nonneg (x : PeriodicDomain) : 0 ≤ cosineProfile x := by
  have ha := (abs_le.mp (cosineKernel_abs_le (1, 0) x)).1
  have hb := (abs_le.mp (cosineKernel_abs_le (0, 1) x)).1
  have hc := (abs_le.mp (cosineKernel_abs_le (1, 3) x)).1
  simp only [cosineProfile, ContinuousMap.add_apply, ContinuousMap.smul_apply,
    ContinuousMap.one_apply, smul_eq_mul]
  linarith

theorem cosineProfile_le_one (x : PeriodicDomain) : cosineProfile x ≤ 1 := by
  have ha := (abs_le.mp (cosineKernel_abs_le (1, 0) x)).2
  have hb := (abs_le.mp (cosineKernel_abs_le (0, 1) x)).2
  have hc := (abs_le.mp (cosineKernel_abs_le (1, 3) x)).2
  simp only [cosineProfile, ContinuousMap.add_apply, ContinuousMap.smul_apply,
    ContinuousMap.one_apply, smul_eq_mul]
  linarith

/-- Cancellation of the sine contributions from each pair of opposite frequencies. -/
theorem cosineProfile_kernel_identity (k : ℤ × ℤ) (x : PeriodicDomain) :
    (∑ s : Fin 7, realProfileWeight s * cosineKernel (k + HierarchicalLaminates.profileStep s) x) =
      cosineProfile x * cosineKernel k x := by
  have ha := cosineKernel_add_pair k (1, 0) x
  have hb := cosineKernel_add_pair k (0, 1) x
  have hc := cosineKernel_add_pair k (1, 3) x
  simp only [sub_eq_add_neg, Prod.neg_mk, neg_zero] at ha hb hc
  norm_num only [realProfileWeight, HierarchicalLaminates.profileWeight, HierarchicalLaminates.profileStep,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue,
    ite_true, ite_false, Fin.reduceEq, Fin.succ_ne_zero, Rat.cast_div, Rat.cast_ofNat,
    cosineProfile, ContinuousMap.add_apply, ContinuousMap.smul_apply,
    ContinuousMap.one_apply, smul_eq_mul, Prod.mk_zero_zero, add_zero]
  linear_combination (1 / 12 : ℝ) * ha + (1 / 12 : ℝ) * hb + (1 / 12 : ℝ) * hc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def cosineSynthesis (f : Coefficients (ℤ × ℤ) E) : C(PeriodicDomain, E) :=
  continuousSynthesis cosineKernel f

def sineSynthesis (f : Coefficients (ℤ × ℤ) E) : C(PeriodicDomain, E) :=
  continuousSynthesis sineKernel f

theorem cosineSynthesis_shift (v : ℤ × ℤ) (f : Coefficients (ℤ × ℤ) E)
    (x : PeriodicDomain) :
    cosineSynthesis (shift v f) x =
      cosineKernel v x • cosineSynthesis f x - sineKernel v x • sineSynthesis f x := by
  have hC := pointwiseSynthesis_summable cosineKernel cosineKernel_norm_le f x
  have hS := pointwiseSynthesis_summable sineKernel sineKernel_norm_le f x
  have hReindex :
      (∑' k : ℤ × ℤ, cosineKernel k x • f (k - v)) =
        ∑' k : ℤ × ℤ, cosineKernel (k + v) x • f k := by
    simpa [subtractEquiv] using
      ((subtractEquiv (-v)).tsum_eq
        (fun k : ℤ × ℤ => cosineKernel k x • f (k - v))).symm
  unfold cosineSynthesis sineSynthesis
  rw [continuousSynthesis_apply cosineKernel cosineKernel_norm_le,
    continuousSynthesis_apply cosineKernel cosineKernel_norm_le,
    continuousSynthesis_apply sineKernel sineKernel_norm_le]
  simp only [shift_apply]
  rw [hReindex]
  calc
    (∑' k : ℤ × ℤ, cosineKernel (k + v) x • f k) =
        ∑' k : ℤ × ℤ, (cosineKernel v x • (cosineKernel k x • f k) -
          sineKernel v x • (sineKernel k x • f k)) := by
      apply tsum_congr
      intro k
      simp [cosineKernel_add, sub_smul, smul_smul, mul_comm]
    _ = (∑' k : ℤ × ℤ, cosineKernel v x • (cosineKernel k x • f k)) -
        ∑' k : ℤ × ℤ, sineKernel v x • (sineKernel k x • f k) :=
      (hC.const_smul _).tsum_sub (hS.const_smul _)
    _ = _ := by rw [hC.tsum_const_smul, hS.tsum_const_smul]

/-- The seven-shift action synthesizes to multiplication by the exact real profile. -/
theorem cosineSynthesis_profileMultiplication (f : Coefficients (ℤ × ℤ) E) :
    cosineSynthesis (profileMultiplication f) = cosineProfile • cosineSynthesis f := by
  have hlinear : cosineSynthesis (profileMultiplication f) =
      ∑ s : Fin 7, realProfileWeight s • cosineSynthesis (shift (HierarchicalLaminates.profileStep s) f) := by
    change (synthesisCLM cosineKernel cosineKernel_norm_le) (profileMultiplication f) = _
    simp only [profileMultiplication, weightedShifts, sum_apply, smul_apply,
      map_sum, map_smul, synthesisCLM_apply, cosineSynthesis]
  rw [hlinear]
  have hca : cosineKernel (-1, 0) = cosineKernel (1, 0) := cosineKernel_neg (1, 0)
  have hcb : cosineKernel (0, -1) = cosineKernel (0, 1) := cosineKernel_neg (0, 1)
  have hcc : cosineKernel (-1, -3) = cosineKernel (1, 3) := cosineKernel_neg (1, 3)
  have hsa : sineKernel (-1, 0) = -sineKernel (1, 0) := sineKernel_neg (1, 0)
  have hsb : sineKernel (0, -1) = -sineKernel (0, 1) := sineKernel_neg (0, 1)
  have hsc : sineKernel (-1, -3) = -sineKernel (1, 3) := sineKernel_neg (1, 3)
  ext x
  norm_num [realProfileWeight, HierarchicalLaminates.profileWeight, HierarchicalLaminates.profileStep,
    Fin.sum_univ_succ, cosineProfile]
  simp_rw [cosineSynthesis_shift]
  simp only [cosineKernel_zero, sineKernel_zero, hca, hcb, hcc, hsa, hsb, hsc,
    ContinuousMap.one_apply, ContinuousMap.zero_apply, ContinuousMap.neg_apply,
    zero_smul, one_smul, sub_zero]
  module

end HierarchicalLaminates.Fourier
