module

public import HierarchicalLaminates.Corrector.FluxCoefficients
public import HierarchicalLaminates.Corrector.SymbolIdentity

/-!
# Synthesis of the physical constitutive equation
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Corrector

open Matrix HierarchicalLaminates.Fourier HierarchicalLaminates.Periodic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

lemma cosineSynthesis_map_of_coeff (f : Coefficients HierarchicalLaminates.Frequency E)
    (g : Coefficients HierarchicalLaminates.Frequency F) (L : E →L[ℝ] F)
    (h : ∀ k, L (f k) = g k) (q : PeriodicDomain) :
    L (cosineSynthesis f q) = cosineSynthesis g q := by
  simp only [cosineSynthesis, continuousSynthesis_apply cosineKernel cosineKernel_norm_le]
  rw [L.map_tsum (pointwiseSynthesis_summable cosineKernel cosineKernel_norm_le f q)]
  apply tsum_congr
  intro k
  rw [map_smul, h]

lemma gradientContinuous_eq_synthesis (f : ReducedCoefficients) (w : ReducedSpace) :
    gradientContinuous f w = cosineSynthesis (gradientVectorCoefficients f w) := by
  ext q ⟨i, a⟩
  exact (cosineSynthesis_map_of_coeff (gradientVectorCoefficients f w)
    (gradientCoefficients f w i a) (EuclideanSpace.proj (𝕜 := ℝ) (i, a))
    (fun k => by
      change gradientVectorCoefficients f w k (i, a) = _
      exact assembleCoefficients_apply _ k (i, a)) q).symm

lemma amplitude_synthesis (f : ReducedCoefficients) (w : ReducedSpace) (a : Fin 16)
    (q : PeriodicDomain) :
    cosineSynthesis (amplitudeCoefficients f w a) q =
      amplitudeOperator w a (cosineSynthesis f q) := by
  symm
  exact cosineSynthesis_map_of_coeff f _ _ (fun _ => rfl) q

def reducedProjection (b : Fin 8) : PhysicalGradient →L[ℝ] ℝ :=
  ∑ a : Fin 16, factorR a b • EuclideanSpace.proj (𝕜 := ℝ) (0, a)

@[simp]
lemma reducedProjection_apply (b : Fin 8) (G : PhysicalGradient) :
    reducedProjection b G = (factorRᵀ *ᵥ (fun a => G (0, a))) b := by
  simp [reducedProjection, Matrix.mulVec, dotProduct]

def reducedEvaluation (w : ReducedSpace) (b : Fin 8) : ReducedOperator →L[ℝ] ℝ :=
  (EuclideanSpace.proj (𝕜 := ℝ) b).comp (ContinuousLinearMap.apply ℝ ReducedSpace w)

def evaluationCoefficients (f : ReducedCoefficients) (w : ReducedSpace) (b : Fin 8) :
    Coefficients HierarchicalLaminates.Frequency ℝ :=
  multiplierCLM (fun _ => reducedEvaluation w b) ‖reducedEvaluation w b‖
    (fun _ X => (reducedEvaluation w b).le_opNorm X) f

lemma reduced_gradient_synthesis (f : ReducedCoefficients) (w : ReducedSpace)
    (q : PeriodicDomain) :
    factorRᵀ *ᵥ (fun a => gradientContinuous f w q (0, a)) =
      (cosineSynthesis (reducedFourierMultiplier f) q) w := by
  ext b
  rw [gradientContinuous_eq_synthesis]
  have h₁ := cosineSynthesis_map_of_coeff (gradientVectorCoefficients f w)
    (evaluationCoefficients (reducedFourierMultiplier f) w b) (reducedProjection b)
    (fun k => by
      rw [reducedProjection_apply]
      simp only [gradientVectorCoefficients, assembleCoefficients_apply]
      exact congrFun (reduced_gradient_coefficients f w k) b) q
  have h₂ := cosineSynthesis_map_of_coeff (reducedFourierMultiplier f)
    (evaluationCoefficients (reducedFourierMultiplier f) w b) (reducedEvaluation w b)
    (fun _ => rfl) q
  exact h₁.trans h₂.symm

lemma response_constitutive_identity (w : ReducedSpace) (q : PeriodicDomain) :
    (HierarchicalLaminates.rho * cosineProfile q) •
      (w + WithLp.toLp 2 (factorRᵀ *ᵥ (fun a => gradientContinuous rhoSolution w q (0, a)))) =
      reducedResponse q w := by
  rw [reduced_gradient_synthesis]
  have h := congrArg (fun M : C(PeriodicDomain, ReducedOperator) => M q w)
    reducedResponse_equation
  simpa only [ContinuousMap.smul_apply, ContinuousMap.smul_apply', ContinuousMap.add_apply,
    ContinuousMap.const_apply, _root_.smul_apply, _root_.add_apply,
    ContinuousLinearMap.id_apply, ← smul_smul] using h.symm

def fluxContinuous (f : ReducedCoefficients) (w : ReducedSpace) :
    C(PeriodicDomain, PhysicalGradient) := cosineSynthesis (fluxCoefficients f w)

lemma fluxContinuous_component (f : ReducedCoefficients) (w : ReducedSpace)
    (i : Fin 2) (a : Fin 16) (q : PeriodicDomain) :
    fluxContinuous f w q (i, a) =
      if i = 0 then gradientComponent f w 0 a q - amplitudeOperator w a (cosineSynthesis f q)
      else HierarchicalLaminates.verticalDiagonalR a * gradientComponent f w 1 a q := by
  have h := cosineSynthesis_map_of_coeff (fluxCoefficients f w)
    (fluxComponentCoefficients f w i a) (EuclideanSpace.proj (𝕜 := ℝ) (i, a))
    (fun k => by
      change fluxCoefficients f w k (i, a) = _
      exact assembleCoefficients_apply _ k (i, a)) q
  change fluxContinuous f w q (i, a) = _ at h
  rw [h]
  by_cases hi : i = 0
  · subst i
    simp only [fluxComponentCoefficients, ↓reduceIte, cosineSynthesis_sub,
      ContinuousMap.sub_apply, amplitude_synthesis]
    rfl
  · simp only [fluxComponentCoefficients, hi, ↓reduceIte, cosineSynthesis_smul,
      ContinuousMap.smul_apply, smul_eq_mul]
    rfl

end HierarchicalLaminates.Corrector
