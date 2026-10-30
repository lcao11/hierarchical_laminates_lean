module

public import HierarchicalLaminates.Finite.OperatorDifference

/-!
# A positive gap for the reduced sequence solution

The finite coefficient values and the infinite-tail bound give a strict
positive loading difference for the convergent reduced response.
-/

@[expose] public section

namespace HierarchicalLaminates

noncomputable section

open Fourier

def sequenceLoading : ReducedCoefficients →L[ℝ] ℝ :=
  operatorDifference.comp (lp.evalCLM ℝ (fun _ : Frequency => ReducedOperator) 1 (0, 0))

theorem sequenceLoading_apply (f : ReducedCoefficients) :
    sequenceLoading f = operatorDifference (f (0, 0)) := rfl

theorem sequenceLoading_bound (f : ReducedCoefficients) :
    |sequenceLoading f| ≤ 2 * ‖f‖ := by
  rw [sequenceLoading_apply]
  exact (operatorDifference_bound _).trans
    (mul_le_mul_of_nonneg_left
      (lp.norm_apply_le_norm (by norm_num : (1 : ENNReal) ≠ 0) f (0, 0)) (by norm_num))

theorem sequenceLoading_term (n : ℕ) :
    sequenceLoading (neumannTerm (contrastIteration rho) rhoSource n) =
      rho ^ (n + 1) * (finiteLoadingCoefficient n : ℝ) := by
  rw [sequenceLoading_apply, rhoTerm_eq_matrixOperator, map_smul, operatorDifference_matrixQ]
  rfl

theorem sequenceLoading_first_five :
    sequenceLoading (∑ n ∈ Finset.range 5, neumannTerm (contrastIteration rho) rhoSource n) =
      2 * kappa * rho ^ 5 := by
  rw [map_sum]
  simp_rw [sequenceLoading_term]
  norm_num [Finset.sum_range_succ, loading_coefficient_one, loading_coefficient_two,
    loading_coefficient_three, loading_coefficient_four, loading_coefficient_five, kappa]
  ring

theorem reduced_solution_gap_error :
    |sequenceLoading rhoSolution - 2 * kappa * rho ^ 5| ≤
      (243 / 256 : ℝ) * kappa * rho ^ 5 := by
  have hbound := sequenceLoading_bound
    (rhoSolution - ∑ n ∈ Finset.range 5, neumannTerm (contrastIteration rho) rhoSource n)
  rw [map_sub, sequenceLoading_first_five] at hbound
  have htail := rhoSolution_tail_five
  have htail' := htail.trans analytic_tail_le
  have hmul := mul_le_mul_of_nonneg_left htail' (by norm_num : (0 : ℝ) ≤ 2)
  have h := hbound.trans hmul
  simpa only [delta_tail_upper_eq] using h

theorem reduced_solution_gap_lower :
    (269 / 256 : ℝ) * kappa * rho ^ 5 ≤ sequenceLoading rhoSolution :=
  smooth_gap_lower reduced_solution_gap_error

theorem reduced_solution_gap_positive : 0 < sequenceLoading rhoSolution :=
  smooth_gap_positive reduced_solution_gap_error

end
end HierarchicalLaminates
