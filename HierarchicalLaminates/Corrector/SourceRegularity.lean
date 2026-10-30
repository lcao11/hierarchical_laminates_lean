module

public import HierarchicalLaminates.Corrector.Source
public import HierarchicalLaminates.Fourier.WeightedRegularity

/-!
# Differentiable source fields for the binary comparison

The constant part and the infinite multiplier response are represented in ℓ¹.
Weighted regularity of the Neumann solution gives summable frequency
derivatives.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Corrector

open Matrix HierarchicalLaminates.Fourier HierarchicalLaminates.Periodic

def sourceCoefficients (z : PotentialVector) (a : Fin 16) :
    Coefficients HierarchicalLaminates.Frequency ℝ :=
  lp.single 1 (0, 0) ((factorR *ᵥ (reducedLoading z : Fin 8 → ℝ)) a) +
    amplitudeCoefficients (reducedFourierMultiplier rhoSolution) (reducedLoading z) a

def sourceDerivativeCoefficients (z : PotentialVector) (a : Fin 16) (i : Fin 2) :
    Coefficients HierarchicalLaminates.Frequency ℝ :=
  amplitudeCoefficients (reducedFourierMultiplier (responseDerivativeCoefficients i))
    (reducedLoading z) a

theorem sourceComponent_eq_synthesis (z : PotentialVector) (a : Fin 16) :
    sourceComponent z a = cosineSynthesis (sourceCoefficients z a) := by
  rw [sourceCoefficients, cosineSynthesis_add, cosineSynthesis_single,
    cosineKernel_zero, one_smul]
  rfl

theorem sourceDerivativeCoefficients_apply (z : PotentialVector) (a : Fin 16)
    (i : Fin 2) (k : HierarchicalLaminates.Frequency) :
    sourceDerivativeCoefficients z a i k =
      -(angularFrequency k i) • sourceCoefficients z a k := by
  have hA : sourceDerivativeCoefficients z a i k =
      -(angularFrequency k i) •
        amplitudeCoefficients (reducedFourierMultiplier rhoSolution) (reducedLoading z) a k := by
    simp only [sourceDerivativeCoefficients, amplitudeCoefficients_apply,
      reducedFourierMultiplier, multiplierCLM_apply, responseDerivativeCoefficients_apply,
      map_smul]
  rw [hA]
  change -(angularFrequency k i) •
      amplitudeCoefficients (reducedFourierMultiplier rhoSolution) (reducedLoading z) a k =
    -(angularFrequency k i) • ((lp.single 1 (0, 0)
      ((factorR *ᵥ (reducedLoading z : Fin 8 → ℝ)) a) :
      Coefficients HierarchicalLaminates.Frequency ℝ) k +
      amplitudeCoefficients (reducedFourierMultiplier rhoSolution) (reducedLoading z) a k)
  by_cases hk : k = (0, 0)
  · subst k
    fin_cases i <;> simp [angularFrequency, frequencyVector]
  · rw [lp.single_apply_ne _ _ _ hk, zero_add]

def sourceDerivative (z : PotentialVector) (a : Fin 16) (i : Fin 2) :
    C(PeriodicDomain, ℝ) :=
  sineSynthesis (sourceDerivativeCoefficients z a i)

theorem sourceComponent_hasDerivAt_flow (z : PotentialVector) (a : Fin 16)
    (i : Fin 2) (q : PeriodicDomain) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => sourceComponent z a (HierarchicalLaminates.Periodic.coordinateFlow i q s))
      (sourceDerivative z a i (HierarchicalLaminates.Periodic.coordinateFlow i q t)) t := by
  rw [sourceComponent_eq_synthesis]
  exact hasDerivAt_cosineSynthesis_flow (sourceCoefficients z a)
    (sourceDerivativeCoefficients z a i) i
    (fun k => sourceDerivativeCoefficients_apply z a i k) q t

theorem sourceDerivative_bounded (z : PotentialVector) (a : Fin 16) (i : Fin 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q, |sourceDerivative z a i q| ≤ C := by
  refine ⟨‖sourceDerivative z a i‖, norm_nonneg (sourceDerivative z a i), ?_⟩
  intro q
  simpa only [Real.norm_eq_abs] using (sourceDerivative z a i).norm_coe_le_norm q

end HierarchicalLaminates.Corrector
