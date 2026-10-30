module

public import HierarchicalLaminates.GClosure.Interfaces

/-! Finite laminate hierarchies retaining the exact overall constituent fraction. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open HierarchicalLaminates.Lamination HierarchicalLaminates.Material HierarchicalLaminates.Homogenization

variable {α : Type*} [Fintype α]

inductive FiniteLaminateAt (L₀ L₁ : Tensor α) : ℝ → Tensor α → Prop
  | phaseZero : FiniteLaminateAt L₀ L₁ 0 L₀
  | phaseOne : FiniteLaminateAt L₀ L₁ 1 L₁
  | layer {θ₁ θ₂ : ℝ} {B₁ B₂ C : Tensor α}
      (n : LayerNormal) (weight : LayerProportion)
      (first : FiniteLaminateAt L₀ L₁ θ₁ B₁)
      (second : FiniteLaminateAt L₀ L₁ θ₂ B₂)
      (minimum : IsLayerTensor B₁ B₂ n weight C) :
      FiniteLaminateAt L₀ L₁ ((weight : ℝ) * θ₁ + (1 - (weight : ℝ)) * θ₂) C

theorem FiniteLaminateAt.forget {L₀ L₁ C : Tensor α} {θ : ℝ}
    (h : FiniteLaminateAt L₀ L₁ θ C) : FiniteLaminate L₀ L₁ C := by
  induction h with
  | phaseZero => exact .phaseZero
  | phaseOne => exact .phaseOne
  | layer n w _ _ hmin ih₁ ih₂ => exact .layer n w ih₁ ih₂ hmin

theorem FiniteLaminateAt.fraction_mem {L₀ L₁ C : Tensor α} {θ : ℝ}
    (h : FiniteLaminateAt L₀ L₁ θ C) : θ ∈ Set.Icc (0 : ℝ) 1 := by
  induction h with
  | phaseZero => constructor <;> norm_num
  | phaseOne => constructor <;> norm_num
  | layer n w _ _ hmin ih₁ ih₂ =>
    constructor
    · exact add_nonneg (mul_nonneg w.property.1 ih₁.1)
        (mul_nonneg (sub_nonneg.mpr w.property.2) ih₂.1)
    · have h₁ := mul_le_mul_of_nonneg_left ih₁.2 w.property.1
      have h₂ := mul_le_mul_of_nonneg_left ih₂.2 (sub_nonneg.mpr w.property.2)
      linarith

def finiteLaminatesAt (L₀ L₁ : Tensor α) (θ : ℝ) : Set (Tensor α) :=
  {C | FiniteLaminateAt L₀ L₁ θ C}

def laminationClosureAt (L₀ L₁ : Tensor α) (θ : ℝ) : Set (Tensor α) :=
  closure (finiteLaminatesAt L₀ L₁ θ)

theorem laminationClosureAt_subset_unrestricted (L₀ L₁ : Tensor α) (θ : ℝ) :
    laminationClosureAt L₀ L₁ θ ⊆ closure (allFiniteLaminates L₀ L₁) := by
  apply closure_mono
  intro C hC
  exact hC.forget

theorem finiteLaminate_has_fraction {L₀ L₁ C : Tensor α}
    (h : FiniteLaminate L₀ L₁ C) : ∃ θ : ℝ, FiniteLaminateAt L₀ L₁ θ C := by
  induction h with
  | phaseZero => exact ⟨0, .phaseZero⟩
  | phaseOne => exact ⟨1, .phaseOne⟩
  | layer n w _ _ hmin ih₁ ih₂ =>
    obtain ⟨θ₁, h₁⟩ := ih₁
    obtain ⟨θ₂, h₂⟩ := ih₂
    exact ⟨_, .layer n w h₁ h₂ hmin⟩

/-- Realization of each layering step implies the fraction-constrained closure inclusion. -/
theorem inclusion_of_layer_realization
    (hlayer : ∀ (θ₁ θ₂ : ℝ), θ₁ ∈ Set.Icc (0 : ℝ) 1 → θ₂ ∈ Set.Icc (0 : ℝ) 1 →
      ∀ (B₁ B₂ : Tensor (Fin 16)), B₁ ∈ GClosure θ₁ → B₂ ∈ GClosure θ₂ →
        ∀ (n : LayerNormal) (w : LayerProportion) (C : Tensor (Fin 16)),
          IsLayerTensor B₁ B₂ n w C → C ∈ GClosure ((w : ℝ)*θ₁+(1-(w : ℝ))*θ₂))
    (θ : ℝ) : laminationClosureAt phaseZero (phaseOne HierarchicalLaminates.rho) θ ⊆ GClosure θ := by
  have hfinite : finiteLaminatesAt phaseZero (phaseOne HierarchicalLaminates.rho) θ ⊆ GClosure θ := by
    intro C hC
    induction hC with
    | phaseZero =>
      exact subset_closure ⟨zeroFraction, zeroFraction_binary, zeroFraction_mean,
        effectiveMatrix_zeroFraction⟩
    | phaseOne =>
      exact subset_closure ⟨oneFraction, oneFraction_binary, oneFraction_mean,
        effectiveMatrix_oneFraction⟩
    | layer n w h₁ h₂ hmin ih₁ ih₂ =>
      exact hlayer _ _ h₁.fraction_mem h₂.fraction_mem _ _ ih₁ ih₂ n w _ hmin
  exact closure_minimal hfinite isClosed_closure

end HierarchicalLaminates.GClosure
