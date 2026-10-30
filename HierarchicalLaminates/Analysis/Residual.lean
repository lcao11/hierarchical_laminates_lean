module

public import HierarchicalLaminates.Analysis.CellProblem

/-!
# Residual bounds for an equilibrated approximate flux

A bounded coercive law controls gradient and flux errors by their constitutive
residual. A contractive mean map then gives a bound for the effective-response
error. These Hilbert-space estimates apply to the equilibrated fluxes used in
the stripe approximation.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Coercivity controls a gradient error from a constitutive residual. -/
theorem gradient_error_bound {A : H →L[ℝ] H} {μ : ℝ}
    (hμ : 0 < μ) (hA : CoerciveLaw A μ) (de r : H)
    (hortho : inner ℝ (A de - r) de = 0) :
    ‖de‖ ≤ ‖r‖ / μ := by
  have heq : inner ℝ (A de) de = inner ℝ r de := by
    simpa only [inner_sub_left, sub_eq_zero] using hortho
  have henergy := hA de
  rw [heq] at henergy
  have hcauchy : inner ℝ r de ≤ ‖r‖ * ‖de‖ := real_inner_le_norm r de
  by_cases hz : ‖de‖ = 0
  · rw [hz]
    positivity
  · have hpos : 0 < ‖de‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    apply (le_div_iff₀ hμ).2
    apply (mul_le_mul_iff_right₀ hpos).mp
    nlinarith

/-- A flux error is small if its constitutive residual is small. -/
theorem flux_error_bound {A : H →L[ℝ] H} {μ M : ℝ}
    (hμ : 0 < μ) (hM : 0 ≤ M) (hA : CoerciveLaw A μ)
    (hbound : ∀ v : H, ‖A v‖ ≤ M * ‖v‖) (de dj r : H)
    (hr : r = A de - dj) (hortho : inner ℝ dj de = 0) :
    ‖dj‖ ≤ (M / μ + 1) * ‖r‖ := by
  have horthor : inner ℝ (A de - r) de = 0 := by
    rw [hr, sub_sub_cancel]
    exact hortho
  have hde := gradient_error_bound hμ hA de r horthor
  have hdj : dj = A de - r := by rw [hr, sub_sub_cancel]
  calc
    ‖dj‖ = ‖A de - r‖ := congrArg norm hdj
    _ ≤ ‖A de‖ + ‖r‖ := norm_sub_le _ _
    _ ≤ M * ‖de‖ + ‖r‖ := by
      have hnorm := hbound de
      linarith
    _ ≤ M * (‖r‖ / μ) + ‖r‖ := by
      have hmul := mul_le_mul_of_nonneg_left hde hM
      linarith
    _ = (M / μ + 1) * ‖r‖ := by ring

/-- The same bound survives a contractive mean map to a loading space. -/
theorem response_error_bound {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {A : H →L[ℝ] H} {μ M : ℝ}
    (mean : H →L[ℝ] E) (hmean : ∀ v : H, ‖mean v‖ ≤ ‖v‖)
    (hμ : 0 < μ) (hM : 0 ≤ M) (hA : CoerciveLaw A μ)
    (hbound : ∀ v : H, ‖A v‖ ≤ M * ‖v‖) (de dj r : H)
    (hr : r = A de - dj) (hortho : inner ℝ dj de = 0) :
    ‖mean dj‖ ≤ (M / μ + 1) * ‖r‖ :=
  (hmean dj).trans (flux_error_bound hμ hM hA hbound de dj r hr hortho)

end HierarchicalLaminates.Analysis
