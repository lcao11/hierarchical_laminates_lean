module

public import HierarchicalLaminates.Fourier.Response
public import HierarchicalLaminates.Finite.ReducedGap

/-!
# Neumann response and fifth-order loading coefficient

The source and iteration both depend on the contrast `r`. For `0 ≤ r < 2 / 3`,
the iteration has contraction bound `3 * r / 2`, giving a convergent response
and an explicit geometric remainder after any finite number of terms.

The rational coefficient recurrence identifies the first five loading terms
with `2 * kappa * r ^ 5`. The remaining error is at most `32 * r ^ 6` on
`0 ≤ r < 1 / 3`. Identification with physical cell energies is established in
`Contrast.CellIdentification`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.Contrast

open Fourier

def source (r : ℝ) : ReducedCoefficients := r • profileSource

/-- The Fourier coefficient response; convergence is proved for `0 ≤ r < 2 / 3`. -/
def solution (r : ℝ) : ReducedCoefficients := neumannSolution (contrastIteration r) (source r)

theorem solution_rho : solution rho = rhoSolution := rfl

theorem contraction_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ 3*r/2 := by positivity

theorem contraction_lt_one {r : ℝ} (hr : r < 2/3) : 3*r/2 < 1 := by linarith

theorem source_norm_le {r : ℝ} (hr : 0 ≤ r) : ‖source r‖ ≤ r := by
  rw [source,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
  exact mul_le_of_le_one_right hr profileSource_norm_le

theorem solution_equation {r : ℝ} (hr : 0 ≤ r) (hrlt : r < 2/3) :
    solution r = source r + contrastIteration r (solution r) :=
  neumannSolution_equation _ (contraction_nonneg hr) (contraction_lt_one hrlt)
    (contrastIteration_norm_le hr) _

theorem solution_tail {r : ℝ} (hr : 0 ≤ r) (hrlt : r < 2/3) (N : ℕ) :
    ‖solution r-∑ n ∈ Finset.range N,neumannTerm (contrastIteration r) (source r) n‖ ≤
      r*(3*r/2)^N/(1-3*r/2) := by
  have ht := neumannSolution_tail (contrastIteration r) (contraction_nonneg hr)
    (contraction_lt_one hrlt) (contrastIteration_norm_le hr) (source r) N
  refine ht.trans ?_
  apply div_le_div_of_nonneg_right _ (by linarith [contraction_lt_one hrlt])
  exact mul_le_mul_of_nonneg_right (source_norm_le hr) (pow_nonneg (contraction_nonneg hr) N)

theorem solution_tail_five {r : ℝ} (hr : 0 ≤ r) (hrlt : r < 2/3) :
    ‖solution r-∑ n ∈ Finset.range 5,neumannTerm (contrastIteration r) (source r) n‖ ≤
      (3/2 : ℝ)^5*r^6/(1-3*r/2) := by
  convert solution_tail hr hrlt 5 using 1; ring

def response (r : ℝ) : C(PeriodicDomain,ReducedOperator) := cosineSynthesis (solution r)

theorem response_rho : response rho = reducedResponse := rfl

theorem response_equation {r : ℝ} (hr : 0 ≤ r) (hrlt : r < 2/3) :
    response r = r • (cosineProfile •
      (ContinuousMap.const PeriodicDomain (ContinuousLinearMap.id ℝ ReducedSpace) +
        cosineSynthesis (reducedFourierMultiplier (solution r)))) := by
  calc
    response r = cosineSynthesis (source r+contrastIteration r (solution r)) :=
      congrArg cosineSynthesis (solution_equation hr hrlt)
    _ = _ := by
      rw [cosineSynthesis_add]
      simp only [source,contrastIteration,smul_apply,ContinuousLinearMap.comp_apply,
        cosineSynthesis_smul,cosineSynthesis_profileMultiplication,profileSource_synthesis]
      ext x
      simp only [ContinuousMap.add_apply,ContinuousMap.smul_apply,
        ContinuousMap.smul_apply',smul_add]

theorem term_eq_matrixOperator (r : ℝ) (n : ℕ) (k : Frequency) :
    neumannTerm (contrastIteration r) (source r) n k =
      r^(n+1) • matrixOperatorQ (neumannCoeffQ n k) := by
  change neumannTerm (r • profileIteration) (r • profileSource) n k = _
  rw [neumannTerm_scale]
  change r^(n+1) • neumannTerm profileIteration profileSource n k = _
  rw [unscaledTerm_eq_matrixOperator]

theorem sequenceLoading_term (r : ℝ) (n : ℕ) :
    sequenceLoading (neumannTerm (contrastIteration r) (source r) n) =
      r^(n+1)*(finiteLoadingCoefficient n : ℝ) := by
  rw [sequenceLoading_apply,term_eq_matrixOperator,map_smul,operatorDifference_matrixQ]
  rfl

/-- The first four loading coefficients vanish and the fifth is `2 * kappa`.
This finite algebraic identity holds for every real `r`. -/
theorem sequenceLoading_first_five (r : ℝ) :
    sequenceLoading (∑ n ∈ Finset.range 5,neumannTerm (contrastIteration r) (source r) n) =
      2*kappa*r^5 := by
  rw [map_sum]
  simp_rw [sequenceLoading_term]
  norm_num [Finset.sum_range_succ,loading_coefficient_one,loading_coefficient_two,
    loading_coefficient_three,loading_coefficient_four,loading_coefficient_five,kappa]
  ring

theorem sequenceLoading_error {r : ℝ} (hr : 0 ≤ r) (hrlt : r < 2/3) :
    |sequenceLoading (solution r)-2*kappa*r^5| ≤
      2*(3/2 : ℝ)^5*r^6/(1-3*r/2) := by
  have hb := sequenceLoading_bound
    (solution r-∑ n ∈ Finset.range 5,neumannTerm (contrastIteration r) (source r) n)
  rw [map_sub,sequenceLoading_first_five] at hb
  exact hb.trans (by
    have ht := mul_le_mul_of_nonneg_left (solution_tail_five hr hrlt) (by norm_num : (0 : ℝ) ≤ 2)
    convert ht using 1; ring)

/-- A uniform sixth-order error bound for the convergent loading response near zero. -/
theorem sequenceLoading_error_uniform {r : ℝ} (hr : 0 ≤ r) (hrlt : r < 1/3) :
    |sequenceLoading (solution r)-2*kappa*r^5| ≤ 32*r^6 := by
  have hr23 : r < 2/3 := by linarith
  refine (sequenceLoading_error hr hr23).trans ?_
  apply (div_le_iff₀ (show 0 < 1-3*r/2 by linarith)).2
  have hpow : 0 ≤ r^6 := by positivity
  nlinarith

end HierarchicalLaminates.Contrast
