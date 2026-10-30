module

public import HierarchicalLaminates.Corrector.CellIdentification
public import HierarchicalLaminates.Corrector.Bounds

/-!
# The bounded source field in the binary realization

The source is `P Pᵀ e_x`, where `e` is the minimizing field. Its series
representation uses bounded maps from the reduced response space.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Corrector

open Matrix HierarchicalLaminates.Fourier HierarchicalLaminates.Periodic

def sourceComponent (z : PotentialVector) (a : Fin 16) : C(PeriodicDomain, ℝ) :=
  ContinuousMap.const PeriodicDomain ((factorR *ᵥ (reducedLoading z : Fin 8 → ℝ)) a) +
    cosineSynthesis (amplitudeCoefficients (reducedFourierMultiplier rhoSolution) (reducedLoading z) a)

lemma sourceComponent_physical (z : PotentialVector) (a : Fin 16) (q : PeriodicDomain) :
    sourceComponent z a q =
      (factorR *ᵥ (factorRᵀ *ᵥ (fun b => totalContinuous z q (0, b)))) a := by
  rw [sourceComponent, ContinuousMap.add_apply, ContinuousMap.const_apply,
    amplitude_synthesis, amplitudeOperator_apply]
  have hred := reduced_gradient_synthesis rhoSolution (reducedLoading z) q
  have hrow : (fun b => totalContinuous z q (0, b)) =
      (z : Fin 16 → ℝ) + (fun b => gradientContinuous rhoSolution (reducedLoading z) q (0, b)) := by
    ext b
    simp [totalContinuous, horizontalLoading]
  rw [hrow, Matrix.mulVec_add, Matrix.mulVec_add]
  rw [hred]
  rfl

lemma sourceComponent_norm_le (z : PotentialVector) (a : Fin 16) :
    ‖sourceComponent z a‖ ≤ |(factorR *ᵥ (reducedLoading z : Fin 8 → ℝ)) a| +
      ‖amplitudeOperator (reducedLoading z) a‖ * ((3 / 2 : ℝ) * ‖rhoSolution‖) := by
  refine (norm_add_le _ _).trans ?_
  apply add_le_add
  · exact (ContinuousMap.norm_le _ (abs_nonneg _)).2 (fun _ => le_rfl)
  · exact (cosineSynthesis_norm_le _).trans
      ((amplitudeCoefficients_norm_le _ _ _).trans
        (mul_le_mul_of_nonneg_left (reducedFourierMultiplier_norm_le _) (norm_nonneg (amplitudeOperator (reducedLoading z) a))))

end HierarchicalLaminates.Corrector
