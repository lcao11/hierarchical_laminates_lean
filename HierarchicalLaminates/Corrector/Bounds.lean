module

public import HierarchicalLaminates.Corrector.Potential

/-! Explicit finite uniform bounds for the physical potential and gradient. -/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Corrector

open HierarchicalLaminates.Fourier

lemma amplitudeCoefficients_norm_le (f : ReducedCoefficients) (w : ReducedSpace)
    (a : Fin 16) :
    ‖amplitudeCoefficients f w a‖ ≤ ‖amplitudeOperator w a‖ * ‖f‖ :=
  multiplierCLM_norm_le _ _ _ f

lemma scalarMultiplier_norm_le (m : HierarchicalLaminates.Frequency → ℝ) (C : ℝ)
    (hm : ∀ k, |m k| ≤ C) (f : Coefficients HierarchicalLaminates.Frequency ℝ) :
    ‖scalarMultiplier m C hm f‖ ≤ C * ‖f‖ :=
  multiplierCLM_norm_le _ _ _ f

lemma gradientCoefficients_norm_le (f : ReducedCoefficients) (w : ReducedSpace)
    (i : Fin 2) (a : Fin 16) :
    ‖gradientCoefficients f w i a‖ ≤ ‖amplitudeOperator w a‖ * ‖f‖ := by
  exact (scalarMultiplier_norm_le _ _ _ _).trans
    (by simpa only [one_mul] using amplitudeCoefficients_norm_le f w a)

lemma potentialCoefficients_norm_le (f : ReducedCoefficients) (w : ReducedSpace)
    (a : Fin 16) :
    ‖potentialCoefficients f w a‖ ≤
      (2 * Real.pi)⁻¹ * (‖amplitudeOperator w a‖ * ‖f‖) := by
  rw [potentialCoefficients, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (scalarMultiplier_norm_le _ _ _ _).trans
    (by simpa only [one_mul] using amplitudeCoefficients_norm_le f w a)

lemma potential_norm_le (f : ReducedCoefficients) (w : ReducedSpace) (a : Fin 16) :
    ‖potential f w a‖ ≤ (2 * Real.pi)⁻¹ * (‖amplitudeOperator w a‖ * ‖f‖) :=
  (continuousSynthesis_norm_le sineKernel sineKernel_norm_le _).trans
    (potentialCoefficients_norm_le f w a)

lemma gradientComponent_norm_le (f : ReducedCoefficients) (w : ReducedSpace)
    (i : Fin 2) (a : Fin 16) :
    ‖gradientComponent f w i a‖ ≤ ‖amplitudeOperator w a‖ * ‖f‖ :=
  (cosineSynthesis_norm_le _).trans (gradientCoefficients_norm_le f w i a)

end HierarchicalLaminates.Corrector
