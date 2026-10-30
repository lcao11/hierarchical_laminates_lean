module

public import HierarchicalLaminates.Fourier.SmoothSynthesis
public import HierarchicalLaminates.Corrector.SourceRegularity
public import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Smooth potentials, gradients and source fields

The amplitude maps and the bounded potential and gradient multipliers preserve
all summable frequency moments. Applying the Banach-valued Fourier synthesis
theorems therefore gives joint C∞ regularity of the periodic fields.

The first results apply to any reduced coefficient sequence satisfying the
moment condition. The remaining results specialize to the fixed-contrast
solution `rhoSolution`, including the full vector gradient, total field and
source components. Every smoothness statement concerns the real periodic lift
and includes mixed spatial derivatives.
-/

@[expose] public section
noncomputable section

namespace HierarchicalLaminates.Corrector

open HierarchicalLaminates.Fourier HierarchicalLaminates.Periodic
open scoped ContDiff

/-- A fixed amplitude operator preserves all summable frequency moments. -/
theorem amplitudeCoefficients_moments {f : ReducedCoefficients} (hf : HasFrequencyMoments f)
    (w : ReducedSpace) (a : Fin 16) : HasFrequencyMoments (amplitudeCoefficients f w a) := by
  apply hf.of_norm_le ‖amplitudeOperator w a‖ (norm_nonneg (amplitudeOperator w a))
  intro k
  exact (amplitudeOperator w a).le_opNorm (f k)

/-- A uniformly bounded scalar multiplier preserves the moment condition. -/
theorem scalarMultiplier_moments {f : Coefficients HierarchicalLaminates.Frequency ℝ}
    (hf : HasFrequencyMoments f) (m : HierarchicalLaminates.Frequency → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hm : ∀ k, |m k| ≤ C) :
    HasFrequencyMoments (scalarMultiplier m C hm f) := by
  apply hf.of_norm_le C hC
  intro k
  rw [scalarMultiplier_apply, norm_mul, Real.norm_eq_abs (m k)]
  exact mul_le_mul_of_nonneg_right (hm k) (norm_nonneg (f k))

theorem potentialCoefficients_moments {f : ReducedCoefficients} (hf : HasFrequencyMoments f)
    (w : ReducedSpace) (a : Fin 16) : HasFrequencyMoments (potentialCoefficients f w a) :=
  (scalarMultiplier_moments (amplitudeCoefficients_moments hf w a)
    _ 1 zero_le_one (fun k => potentialMultiplier_abs_le k a)).smul _

theorem gradientCoefficients_moments {f : ReducedCoefficients} (hf : HasFrequencyMoments f)
    (w : ReducedSpace) (i : Fin 2) (a : Fin 16) : HasFrequencyMoments (gradientCoefficients f w i a) :=
  scalarMultiplier_moments (amplitudeCoefficients_moments hf w a)
    _ 1 zero_le_one (fun k => gradientMultiplier_abs_le k i a)

/-- The potential's periodic real lift is jointly smooth for every coefficient
sequence with all summable frequency moments. -/
theorem potential_smooth_of_moments (f : ReducedCoefficients) (hf : HasFrequencyMoments f)
    (w : ReducedSpace) (a : Fin 16) : ContDiff ℝ ∞ (realLift (potential f w a)) :=
  sineSynthesis_smooth _ (potentialCoefficients_moments hf w a)

/-- Each spatial and potential component of the gradient has a jointly smooth real lift. -/
theorem gradientComponent_smooth_of_moments (f : ReducedCoefficients) (hf : HasFrequencyMoments f)
    (w : ReducedSpace) (i : Fin 2) (a : Fin 16) :
    ContDiff ℝ ∞ (realLift (gradientComponent f w i a)) :=
  cosineSynthesis_smooth _ (gradientCoefficients_moments hf w i a)

/-- The whole physical gradient has joint C∞ real lift, including every mixed derivative. -/
theorem gradientContinuous_smooth_of_moments (f : ReducedCoefficients) (hf : HasFrequencyMoments f)
    (w : ReducedSpace) : ContDiff ℝ ∞ (torusLift (gradientContinuous f w)) := by
  apply (contDiff_piLp 2).2
  intro c
  rcases c with ⟨i, a⟩
  exact gradientComponent_smooth_of_moments f hf w i a

/-- The sixteen potential components form a jointly smooth Euclidean-valued lift. -/
theorem potentialVector_smooth_of_moments (f : ReducedCoefficients) (hf : HasFrequencyMoments f)
    (w : ReducedSpace) :
    ContDiff ℝ ∞ (fun x : LiftDomain => WithLp.toLp 2
      (fun a : Fin 16 => potential f w a (fun i => (x i : UnitAddCircle)))) := by
  apply (contDiff_piLp 2).2
  intro a
  exact potential_smooth_of_moments f hf w a

/-- Smoothness of each potential component for the fixed-contrast corrector. -/
theorem smoothCorrector_potential_smooth (w : ReducedSpace) (a : Fin 16) :
    ContDiff ℝ ∞ (realLift (potential rhoSolution w a)) :=
  potential_smooth_of_moments _ rhoSolution_frequency_moment_summable w a

/-- Smoothness of the full fixed-contrast physical gradient. -/
theorem smoothCorrector_gradient_smooth (w : ReducedSpace) :
    ContDiff ℝ ∞ (torusLift (gradientContinuous rhoSolution w)) :=
  gradientContinuous_smooth_of_moments _ rhoSolution_frequency_moment_summable w

/-- Adding the constant loading preserves joint smoothness of the physical field. -/
theorem totalContinuous_smooth (z : PotentialVector) :
    ContDiff ℝ ∞ (torusLift (totalContinuous z)) :=
  contDiff_const.add (smoothCorrector_gradient_smooth (reducedLoading z))

/-- The multiplier response has a jointly smooth periodic real lift. -/
theorem multiplierResponse_smooth : ContDiff ℝ ∞ (torusLift multiplierResponse) :=
  cosineSynthesis_smooth _ (reducedFourierMultiplier_moments rhoSolution_frequency_moment_summable)

/-- Each source component is the sum of a constant and a jointly smooth Fourier field. -/
theorem sourceComponent_smooth (z : PotentialVector) (a : Fin 16) :
    ContDiff ℝ ∞ (realLift (sourceComponent z a)) := by
  have hs := cosineSynthesis_smooth
    (amplitudeCoefficients (reducedFourierMultiplier rhoSolution) (reducedLoading z) a)
    (amplitudeCoefficients_moments
      (reducedFourierMultiplier_moments rhoSolution_frequency_moment_summable) (reducedLoading z) a)
  exact contDiff_const.add hs

end HierarchicalLaminates.Corrector
