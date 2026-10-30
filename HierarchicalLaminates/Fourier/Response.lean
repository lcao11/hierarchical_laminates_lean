module

public import HierarchicalLaminates.Fourier.Mean
public import HierarchicalLaminates.Fourier.SymbolMultiplier

/-!
# The continuous reduced response and its mean remainder

Uniform synthesis of the infinite coefficient solution gives a continuous
field satisfying the multiplication equation for the cosine profile and the
mean remainder estimate.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Fourier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem cosineSynthesis_single (k : ℤ × ℤ) (v : E) :
    cosineSynthesis (lp.single 1 k v) = cosineKernel k • ContinuousMap.const PeriodicDomain v := by
  ext x
  rw [cosineSynthesis, continuousSynthesis_apply cosineKernel cosineKernel_norm_le,
    tsum_eq_single k]
  · simp only [lp.single_apply_self]
    rfl
  · intro j hj
    simp only [lp.single_apply_ne _ _ _ hj, smul_zero]

theorem cosineSynthesis_add (f g : Coefficients (ℤ × ℤ) E) :
    cosineSynthesis (f + g) = cosineSynthesis f + cosineSynthesis g :=
  (synthesisCLM cosineKernel cosineKernel_norm_le).map_add f g

theorem cosineSynthesis_smul (c : ℝ) (f : Coefficients (ℤ × ℤ) E) :
    cosineSynthesis (c • f) = c • cosineSynthesis f :=
  (synthesisCLM cosineKernel cosineKernel_norm_le).map_smul c f

theorem cosineSynthesis_sub (f g : Coefficients (ℤ × ℤ) E) :
    cosineSynthesis (f - g) = cosineSynthesis f - cosineSynthesis g :=
  (synthesisCLM cosineKernel cosineKernel_norm_le).map_sub f g

omit [CompleteSpace E] in
theorem cosineSynthesis_norm_le (f : Coefficients (ℤ × ℤ) E) :
    ‖cosineSynthesis f‖ ≤ ‖f‖ :=
  continuousSynthesis_norm_le cosineKernel cosineKernel_norm_le f

def reducedResponse : C(PeriodicDomain, ReducedOperator) := cosineSynthesis rhoSolution

def reducedResponseApproximation (N : ℕ) : C(PeriodicDomain, ReducedOperator) :=
  cosineSynthesis (∑ n ∈ Finset.range N, neumannTerm (contrastIteration HierarchicalLaminates.rho) rhoSource n)

theorem profileSource_synthesis :
    cosineSynthesis profileSource =
      cosineProfile • ContinuousMap.const PeriodicDomain (ContinuousLinearMap.id ℝ ReducedSpace) := by
  rw [profileSource, cosineSynthesis_profileMultiplication, cosineSynthesis_single,
    cosineKernel_zero, one_smul]

theorem reducedResponse_equation :
    reducedResponse = HierarchicalLaminates.rho •
      (cosineProfile •
        (ContinuousMap.const PeriodicDomain (ContinuousLinearMap.id ℝ ReducedSpace) +
          cosineSynthesis (reducedFourierMultiplier rhoSolution))) := by
  calc
    reducedResponse = cosineSynthesis
        (rhoSource + contrastIteration HierarchicalLaminates.rho rhoSolution) :=
      congrArg cosineSynthesis rhoSolution_equation
    _ = _ := by
      rw [cosineSynthesis_add]
      simp only [rhoSource, contrastIteration, smul_apply,
        ContinuousLinearMap.comp_apply, cosineSynthesis_smul,
        cosineSynthesis_profileMultiplication, profileSource_synthesis]
      ext x
      simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply,
        ContinuousMap.smul_apply', smul_add]

theorem reducedResponse_mean : uniformMean reducedResponse = rhoSolution (0, 0) :=
  cosineSynthesis_mean rhoSolution

theorem reducedResponse_tail (N : ℕ) :
    ‖reducedResponse - reducedResponseApproximation N‖ ≤
      HierarchicalLaminates.rho * (3 * HierarchicalLaminates.rho / 2) ^ N / (1 - 3 * HierarchicalLaminates.rho / 2) := by
  rw [reducedResponse, reducedResponseApproximation, ← cosineSynthesis_sub]
  exact (cosineSynthesis_norm_le _).trans (rhoSolution_tail N)

theorem reducedResponse_tail_five :
    ‖reducedResponse - reducedResponseApproximation 5‖ ≤
      (3 / 2 : ℝ) ^ 5 * HierarchicalLaminates.rho ^ 6 / (1 - 3 * HierarchicalLaminates.rho / 2) := by
  rw [reducedResponse, reducedResponseApproximation, ← cosineSynthesis_sub]
  exact (cosineSynthesis_norm_le _).trans rhoSolution_tail_five

theorem rhoSolution_coefficient_tail_five (k : HierarchicalLaminates.Frequency) :
    ‖rhoSolution k -
      (∑ n ∈ Finset.range 5, neumannTerm (contrastIteration HierarchicalLaminates.rho) rhoSource n) k‖ ≤
      (3 / 2 : ℝ) ^ 5 * HierarchicalLaminates.rho ^ 6 / (1 - 3 * HierarchicalLaminates.rho / 2) := by
  exact (lp.norm_apply_le_norm (by norm_num) _ k).trans rhoSolution_tail_five

end HierarchicalLaminates.Fourier
