module

public import HierarchicalLaminates.GClosure.DimensionEnergy
public import HierarchicalLaminates.GClosure.DimensionReindex

/-!
# Exact-fraction G-closure for arbitrary finite potential indices
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material HierarchicalLaminates.Lamination
  HierarchicalLaminates.Homogenization

def genericBinaryTensors {α : Type*} [Fintype α] (L₀ L₁ : Tensor α) (θ : ℝ) :
    Set (Tensor α) :=
  {C | C.IsHermitian ∧ ∃ b : PhaseFraction, IsBinary b ∧ phaseMean b = θ ∧
    ∀ F : Gradient α, quadraticEnergy C F = genericCellEnergy L₀ L₁ b F}

def genericGClosure {α : Type*} [Fintype α] (L₀ L₁ : Tensor α) (θ : ℝ) :
    Set (Tensor α) := closure (genericBinaryTensors L₀ L₁ θ)

theorem genericBinaryTensors_sixteen (θ : ℝ) :
    genericBinaryTensors phaseZero (phaseOne rho) θ = periodicBinaryTensors θ := by
  ext C
  constructor
  · rintro ⟨hC,b,hb,hm,henergy⟩
    refine ⟨b,hb,hm,?_⟩
    apply hermitian_eq_of_quadratic_eq (effectiveMatrix_isHermitian b) hC
    intro F
    change quadraticEnergy (effectiveMatrix b) F = quadraticEnergy C F
    rw [henergy F, genericCellEnergy_sixteen]
    exact effectiveMatrix_quadratic_energy b (physicalLoading F)
  · rintro ⟨b,hb,hm,rfl⟩
    refine ⟨effectiveMatrix_isHermitian b,b,hb,hm,?_⟩
    intro F
    rw [genericCellEnergy_sixteen]
    exact effectiveMatrix_quadratic_energy b (physicalLoading F)

theorem genericGClosure_sixteen (θ : ℝ) :
    genericGClosure phaseZero (phaseOne rho) θ = GClosure θ := by
  rw [genericGClosure, genericBinaryTensors_sixteen]
  rfl

theorem genericGClosure_extend {β : Type*} [Fintype β] (θ : ℝ)
    {C : Tensor (Fin 16)} (hC : C ∈ GClosure θ) :
    extendTensor (β := β) C ∈ genericGClosure (extendTensor phaseZero)
      (extendTensor (phaseOne rho)) θ := by
  have hclosed : IsClosed {C : Tensor (Fin 16) | extendTensor (β := β) C ∈
      genericGClosure (extendTensor phaseZero) (extendTensor (phaseOne rho)) θ} :=
    isClosed_closure.preimage extendTensor_continuous
  apply closure_minimal (fun B hB => ?_) hclosed hC
  rcases hB with ⟨b,hb,hm,rfl⟩
  exact subset_closure ⟨extendTensor_isHermitian (effectiveMatrix_isHermitian b),
    b,hb,hm,extended_effective_energy b⟩

theorem genericBinaryTensors_reindex {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (L₀ L₁ : Tensor α) (θ : ℝ) {C : Tensor α}
    (hC : C ∈ genericBinaryTensors L₀ L₁ θ) :
    reindexTensor e C ∈ genericBinaryTensors (reindexTensor e L₀) (reindexTensor e L₁) θ := by
  rcases hC with ⟨hCh,b,hb,hm,henergy⟩
  refine ⟨reindexTensor_isHermitian e hCh,b,hb,hm,?_⟩
  intro F
  rw [← reindexGradient_symm e F, quadraticEnergy_reindex, genericCellEnergy_reindex]
  exact henergy _

theorem genericGClosure_reindex {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (L₀ L₁ : Tensor α) (θ : ℝ) {C : Tensor α}
    (hC : C ∈ genericGClosure L₀ L₁ θ) :
    reindexTensor e C ∈ genericGClosure (reindexTensor e L₀) (reindexTensor e L₁) θ := by
  have hclosed : IsClosed {C : Tensor α |
      reindexTensor e C ∈ genericGClosure (reindexTensor e L₀) (reindexTensor e L₁) θ} :=
    isClosed_closure.preimage (reindexTensor_continuous e)
  apply closure_minimal (fun B hB => ?_) hclosed hC
  exact subset_closure (genericBinaryTensors_reindex e L₀ L₁ θ hB)

end HierarchicalLaminates.GClosure
