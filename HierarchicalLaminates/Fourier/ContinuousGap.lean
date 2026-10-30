module

public import HierarchicalLaminates.Fourier.Response
public import HierarchicalLaminates.Finite.ReducedGap

/-!
# A positive loading gap for the continuous reduced response

Uniform synthesis transfers the coefficient-space solution and its mean
loading difference to the normalized periodic domain.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Fourier

theorem reducedResponse_mean_gap :
    HierarchicalLaminates.operatorDifference (uniformMean reducedResponse) =
      HierarchicalLaminates.sequenceLoading rhoSolution := by
  rw [reducedResponse_mean, HierarchicalLaminates.sequenceLoading_apply]

theorem reducedResponse_mean_gap_error :
    |HierarchicalLaminates.operatorDifference (uniformMean reducedResponse) -
      2 * HierarchicalLaminates.kappa * HierarchicalLaminates.rho ^ 5| ≤
      (243 / 256 : ℝ) * HierarchicalLaminates.kappa * HierarchicalLaminates.rho ^ 5 := by
  rw [reducedResponse_mean_gap]
  exact HierarchicalLaminates.reduced_solution_gap_error

theorem reducedResponse_mean_gap_lower :
    (269 / 256 : ℝ) * HierarchicalLaminates.kappa * HierarchicalLaminates.rho ^ 5 ≤
      HierarchicalLaminates.operatorDifference (uniformMean reducedResponse) := by
  rw [reducedResponse_mean_gap]
  exact HierarchicalLaminates.reduced_solution_gap_lower

theorem reducedResponse_mean_gap_positive :
    0 < HierarchicalLaminates.operatorDifference (uniformMean reducedResponse) := by
  rw [reducedResponse_mean_gap]
  exact HierarchicalLaminates.reduced_solution_gap_positive

end HierarchicalLaminates.Fourier
