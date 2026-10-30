module

public import HierarchicalLaminates.Composition.Seed
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Tensor closure from simultaneous approximation of the coordinate responses. -/

@[expose] public section
noncomputable section

namespace HierarchicalLaminates.Composition

open MeasureTheory Matrix Filter HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material
  HierarchicalLaminates.Lamination HierarchicalLaminates.Homogenization

def coordinateLoading (j : Fin 2 × Fin 16) : PhysicalGradient :=
  WithLp.toLp 2 (Pi.single j (1 : ℝ))

theorem tensor_coordinateLoading (B : PhysicalTensor) (i j : Fin 2 × Fin 16) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) B (coordinateLoading j) i = B i j := by
  change (B *ᵥ Pi.single j (1 : ℝ)) i = B i j
  simp only [Matrix.mulVec_single_one, Matrix.col_apply]

theorem recovery_convergence_of_responses (b : PhaseFraction) (θ : ℝ)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ r k : ℕ, 0 < r ∧ 0 < k ∧
      ∀ j : Fin 2 × Fin 16,
        ‖HierarchicalLaminates.Material.effectiveOperator (thetaRecovery b θ r k) (coordinateLoading j) -
          Matrix.toEuclideanCLM (𝕜 := ℝ) (arithmeticCandidate θ (effectiveMatrix b))
            (coordinateLoading j)‖ < ε) :
    ∃ r k : ℕ → ℕ, (∀ n, 0 < r n) ∧ (∀ n, 0 < k n) ∧
      Tendsto (fun n => effectiveMatrix (thetaRecovery b θ (r n) (k n)))
        atTop (nhds (arithmeticCandidate θ (effectiveMatrix b))) := by
  choose r k hr hk happ using (fun n : ℕ =>
    happrox (1 / ((n : ℝ) + 1)) (by positivity))
  have hlim : Tendsto (fun n => effectiveMatrix (thetaRecovery b θ (r n) (k n)))
      atTop (nhds (arithmeticCandidate θ (effectiveMatrix b))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _)
      (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    have hi := (PiLp.norm_apply_le
      (HierarchicalLaminates.Material.effectiveOperator (thetaRecovery b θ (r n) (k n)) (coordinateLoading j) -
        Matrix.toEuclideanCLM (𝕜 := ℝ) (arithmeticCandidate θ (effectiveMatrix b))
          (coordinateLoading j)) i).trans ((happ n j).le)
    rw [← effectiveMatrix_operator] at hi
    simpa only [PiLp.sub_apply, tensor_coordinateLoading] using hi
  exact ⟨r, k, hr, hk, hlim⟩

theorem candidate_mem_GClosure_of_responses (b : PhaseFraction) (hb : IsBinary b)
    (hm : phaseMean b = 1 / 2) {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ r k : ℕ, 0 < r ∧ 0 < k ∧
      ∀ j : Fin 2 × Fin 16,
        ‖HierarchicalLaminates.Material.effectiveOperator (thetaRecovery b θ r k) (coordinateLoading j) -
          Matrix.toEuclideanCLM (𝕜 := ℝ) (arithmeticCandidate θ (effectiveMatrix b))
            (coordinateLoading j)‖ < ε) :
    arithmeticCandidate θ (effectiveMatrix b) ∈ GClosure θ := by
  obtain ⟨r, k, hr, hk, hlim⟩ := recovery_convergence_of_responses b θ happrox
  apply isClosed_closure.mem_of_tendsto hlim
  exact Filter.Eventually.of_forall fun n => subset_closure
    ⟨thetaRecovery b θ (r n) (k n), thetaRecovery_isBinary b hb θ (r n) (k n),
      thetaRecovery_mean b hm hθ₀ hθ₁ (hr n) (hk n), rfl⟩

end HierarchicalLaminates.Composition
