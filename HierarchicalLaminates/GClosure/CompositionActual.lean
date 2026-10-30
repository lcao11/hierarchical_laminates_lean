module

public import HierarchicalLaminates.GClosure.TwoChildTrials
public import HierarchicalLaminates.Composition.Closure
public import HierarchicalLaminates.GClosure.GClosureComposition

/-!
# Realizing layers of two periodic two-phase materials
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open MeasureTheory Set Filter HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material
  HierarchicalLaminates.Lamination HierarchicalLaminates.Homogenization HierarchicalLaminates.Composition

theorem tensor_mem_GClosure_of_response_approx (θ : ℝ) (C : PhysicalTensor)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ b : PhaseFraction, IsBinary b ∧ phaseMean b = θ ∧
      ∀ j : Fin 2 × Fin 16,
        ‖HierarchicalLaminates.Material.effectiveOperator b (coordinateLoading j) -
          Matrix.toEuclideanCLM (𝕜 := ℝ) C (coordinateLoading j)‖ < ε) :
    C ∈ GClosure θ := by
  choose bs hb hm happ using (fun n : ℕ => happrox (1/((n : ℝ)+1)) (by positivity))
  have hlim : Tendsto (fun n => effectiveMatrix (bs n)) atTop (nhds C) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hi := (PiLp.norm_apply_le
      (HierarchicalLaminates.Material.effectiveOperator (bs n) (coordinateLoading j) -
        Matrix.toEuclideanCLM (𝕜 := ℝ) C (coordinateLoading j)) i).trans ((happ n j).le)
    rw [← effectiveMatrix_operator] at hi
    simpa only [PiLp.sub_apply,tensor_coordinateLoading] using hi
  apply isClosed_closure.mem_of_tendsto hlim
  exact Filter.Eventually.of_forall fun n => subset_closure ⟨bs n,hb n,hm n,rfl⟩

theorem twoChild_responses_approx (R : TorusCoordinates) (b c : PhaseFraction)
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ r₁ k₁ r₂ k₂ : ℕ, 0 < r₁ ∧ 0 < k₁ ∧ 0 < r₂ ∧ 0 < k₂ ∧
      ∀ j : Fin 2 × Fin 16,
        ‖HierarchicalLaminates.Material.effectiveOperator (twoChildRecovery R b c a r₁ k₁ r₂ k₂)
            (coordinateLoading j) - Matrix.toEuclideanCLM (𝕜 := ℝ)
          (computedLayerTensor (effectiveMatrix b) (effectiveMatrix c) (coordinateNormal R) a)
            (coordinateLoading j)‖ < ε := by
  choose u₁ ψ₁ hm₁ using fun j : Fin 2 × Fin 16 =>
    exists_regular_microscopic_approx b (firstChildLoading R b c a (coordinateLoading j))
      (ε/100) (by positivity)
  choose u₂ ψ₂ hm₂ using fun j : Fin 2 × Fin 16 =>
    exists_regular_microscopic_approx c (secondChildLoading R b c a (coordinateLoading j))
      (ε/100) (by positivity)
  obtain ⟨δ₁,hδ₁,r₁,hr₁,k₁,hk₁,hlocal₁⟩ := exists_common_oblique_localization R a ha₀ ha₁.le
    u₁ ψ₁ (ε/100) (by positivity)
  obtain ⟨δ₂,hδ₂,r₂,hr₂,k₂,hk₂,hlocal₂⟩ := exists_common_complementary_localization R a ha₀ ha₁
    u₂ ψ₂ (ε/100) (by positivity)
  refine ⟨r₁,k₁,r₂,k₂,hr₁,hk₁,hr₂,hk₂,?_⟩
  intro j
  have h := twoChild_response_error_bound R b c a ha₀ ha₁ hr₁ hk₁ hr₂ hk₂ (coordinateLoading j)
    (u₁ j) (ψ₁ j) (u₂ j) (ψ₂ j)
    (obliqueLocalizedPotential R ha₀ ha₁.le hδ₁ hr₁ k₁ (u₁ j))
    (obliqueLocalizedPotential R ha₀ ha₁.le hδ₁ hr₁ k₁ (ψ₁ j))
    (complementaryLocalizedPotential R a ha₀ ha₁ hδ₂ hr₂ k₂ (u₂ j))
    (complementaryLocalizedPotential R a ha₀ ha₁ hδ₂ hr₂ k₂ (ψ₂ j))
  have h₁ := hm₁ j
  have h₂ := hm₂ j
  have h₃ := hlocal₁ j
  have h₄ := hlocal₂ j
  linarith

/-- A physical layer in every periodic integer direction is realized at its exact weighted fraction. -/
theorem actual_integer_layer_mem_GClosure (b c : PhaseFraction) (hb : IsBinary b)
    (hc : IsBinary c) (R : TorusCoordinates) (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) :
    computedLayerTensor (effectiveMatrix b) (effectiveMatrix c) (coordinateNormal R) a ∈
      GClosure (a * phaseMean b + (1-a) * phaseMean c) := by
  apply tensor_mem_GClosure_of_response_approx
  intro ε hε
  obtain ⟨r₁,k₁,r₂,k₂,hr₁,hk₁,hr₂,hk₂,hresponse⟩ :=
    twoChild_responses_approx R b c a ha₀ ha₁ ε hε
  exact ⟨twoChildRecovery R b c a r₁ k₁ r₂ k₂,
    twoChildRecovery_binary R b c hb hc a r₁ k₁ r₂ k₂,
    twoChildRecovery_mean R b c ha₀ ha₁ hr₁ hk₁ hr₂ hk₂,hresponse⟩

theorem actual_layer_realization : ActualLayerRealization :=
  fun b c hb hc R a ha₀ ha₁ => actual_integer_layer_mem_GClosure b c hb hc R a ha₀ ha₁

end HierarchicalLaminates.GClosure
