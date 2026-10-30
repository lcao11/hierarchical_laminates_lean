module

public import HierarchicalLaminates.Composition.Closure
public import HierarchicalLaminates.Composition.MicroscopicApproximation
public import HierarchicalLaminates.Composition.FiniteLocalization
public import HierarchicalLaminates.Composition.TrialFields

/-!
# Exact-fraction composition by periodic two-phase arrangements
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.Composition

open MeasureTheory Filter HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material
  HierarchicalLaminates.Lamination HierarchicalLaminates.Homogenization

theorem recovery_responses_approx (b : PhaseFraction) (θ : ℝ)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ r k : ℕ, 0 < r ∧ 0 < k ∧ ∀ j : Fin 2 × Fin 16,
      ‖HierarchicalLaminates.Material.effectiveOperator (thetaRecovery b θ r k) (coordinateLoading j) -
        Matrix.toEuclideanCLM (𝕜 := ℝ) (arithmeticCandidate θ (effectiveMatrix b))
          (coordinateLoading j)‖ < ε := by
  choose u ψ hmicro using fun j : Fin 2 × Fin 16 =>
    exists_regular_microscopic_approx b (coordinateLoading j) (ε / 20) (by positivity)
  obtain ⟨δ, hδ, r, hr, k, hk, hlocal⟩ := exists_common_localization
    (layerFraction θ) (layerFraction_pos hθ₀ hθ₁) (layerFraction_le_one θ)
    u ψ (ε / 20) (by positivity)
  refine ⟨r, k, hr, hk, ?_⟩
  intro j
  have hresponse := recovery_response_error_bound b θ δ hθ₀ hθ₁ hδ r hr k hk
    (coordinateLoading j) (u j) (ψ j)
  have hm := hmicro j
  have hl := hlocal j
  linarith

/-- The full effective matrix converges. Binary half-fraction seeds retain the
requested fraction exactly at every recovery scale. -/
theorem recovery_matrix_convergence (b : PhaseFraction) (θ : ℝ)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    ∃ r k : ℕ → ℕ, (∀ n, 0 < r n) ∧ (∀ n, 0 < k n) ∧
      Tendsto (fun n => effectiveMatrix (thetaRecovery b θ (r n) (k n)))
        atTop (nhds (arithmeticCandidate θ (effectiveMatrix b))) :=
  recovery_convergence_of_responses b θ (recovery_responses_approx b θ hθ₀ hθ₁)

theorem half_fraction_composition_mem_GClosure (b : PhaseFraction) (hb : IsBinary b)
    (hm : phaseMean b = 1 / 2) (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    arithmeticCandidate θ (effectiveMatrix b) ∈ GClosure θ :=
  candidate_mem_GClosure_of_responses b hb hm hθ₀ hθ₁
    (recovery_responses_approx b θ hθ₀ hθ₁)

/-- The selected seed realizes every requested arithmetic layer in G-closure. -/
theorem seed_composition_mem_GClosure (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    arithmeticCandidate θ (effectiveMatrix seedFraction) ∈ GClosure θ :=
  half_fraction_composition_mem_GClosure seedFraction seedFraction_binary seedFraction_mean
    θ hθ₀ hθ₁

end HierarchicalLaminates.Composition
