module

public import HierarchicalLaminates.GClosure.DimensionReindex
public import HierarchicalLaminates.GClosure.FractionHierarchy

/-! Relabeling potential components preserves every variational lamination step and its closure. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open HierarchicalLaminates.Lamination

def reindexJump {α β : Type*} (e : α ≃ β) (z : α → ℝ) : β → ℝ :=
  fun b => z (e.symm b)

theorem reindexJump_symm {α β : Type*} (e : α ≃ β) (z : β → ℝ) :
    reindexJump e (reindexJump e.symm z) = z := by
  funext a
  simp [reindexJump]

theorem firstLayerField_reindex {α β : Type*} (e : α ≃ β)
    (n : LayerNormal) (w : ℝ) (F : Gradient α) (z : α → ℝ) :
    firstLayerField n w (reindexGradient e F) (reindexJump e z) =
      reindexGradient e (firstLayerField n w F z) := rfl

theorem secondLayerField_reindex {α β : Type*} (e : α ≃ β)
    (n : LayerNormal) (w : ℝ) (F : Gradient α) (z : α → ℝ) :
    secondLayerField n w (reindexGradient e F) (reindexJump e z) =
      reindexGradient e (secondLayerField n w F z) := rfl

theorem layerEnergy_reindex {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (B C : Tensor α) (n : LayerNormal) (w : ℝ)
    (F : Gradient α) (z : α → ℝ) :
    layerEnergy (reindexTensor e B) (reindexTensor e C) n w
      (reindexGradient e F) (reindexJump e z) = layerEnergy B C n w F z := by
  rw [layerEnergy,firstLayerField_reindex,secondLayerField_reindex,
    quadraticEnergy_reindex,quadraticEnergy_reindex]
  rfl

theorem layerTensor_reindex {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) {B C D : Tensor α} {n : LayerNormal} {w : LayerProportion}
    (hD : IsLayerTensor B C n w D) :
    IsLayerTensor (reindexTensor e B) (reindexTensor e C) n w (reindexTensor e D) := by
  refine ⟨reindexTensor_isHermitian e hD.1, ?_⟩
  intro F
  have h := hD.2 (reindexGradient e.symm F)
  constructor
  · obtain ⟨z,hz⟩ := h.1
    refine ⟨reindexJump e z, ?_⟩
    rw [← reindexGradient_symm e F,layerEnergy_reindex,quadraticEnergy_reindex]
    exact hz
  · rintro _ ⟨z,rfl⟩
    rw [← reindexGradient_symm e F,← reindexJump_symm e z,
      layerEnergy_reindex,quadraticEnergy_reindex]
    exact h.2 ⟨reindexJump e.symm z,rfl⟩

theorem reindexTensor_symm {α β : Type*} (e : α ≃ β) (C : Tensor β) :
    reindexTensor e (reindexTensor e.symm C) = C := by
  ext ⟨i,a⟩ ⟨j,b⟩
  simp [reindexTensor,componentEquiv]

theorem reindexTensor_symm_left {α β : Type*} (e : α ≃ β) (C : Tensor α) :
    reindexTensor e.symm (reindexTensor e C) = C := by
  simpa only [Equiv.symm_symm] using reindexTensor_symm e.symm C

theorem finiteLaminate_reindex {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) {L₀ L₁ C : Tensor α} (h : FiniteLaminate L₀ L₁ C) :
    FiniteLaminate (reindexTensor e L₀) (reindexTensor e L₁) (reindexTensor e C) := by
  induction h with
  | phaseZero => exact .phaseZero
  | phaseOne => exact .phaseOne
  | layer n w _ _ hmin ih₁ ih₂ => exact .layer n w ih₁ ih₂ (layerTensor_reindex e hmin)

theorem finiteLaminateAt_reindex {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) {L₀ L₁ C : Tensor α} {θ : ℝ} (h : FiniteLaminateAt L₀ L₁ θ C) :
    FiniteLaminateAt (reindexTensor e L₀) (reindexTensor e L₁) θ (reindexTensor e C) := by
  induction h with
  | phaseZero => exact .phaseZero
  | phaseOne => exact .phaseOne
  | layer n w _ _ hmin ih₁ ih₂ => exact .layer n w ih₁ ih₂ (layerTensor_reindex e hmin)

theorem laminateClosure_reindex {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (L₀ L₁ : Tensor α) {C : Tensor α}
    (hC : C ∈ closure (allFiniteLaminates L₀ L₁)) :
    reindexTensor e C ∈ closure (allFiniteLaminates (reindexTensor e L₀) (reindexTensor e L₁)) := by
  have hclosed : IsClosed {C : Tensor α | reindexTensor e C ∈
      closure (allFiniteLaminates (reindexTensor e L₀) (reindexTensor e L₁))} :=
    isClosed_closure.preimage (reindexTensor_continuous e)
  apply closure_minimal (fun B hB => ?_) hclosed hC
  exact subset_closure (finiteLaminate_reindex e hB)

theorem laminateClosure_reindex_iff {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (L₀ L₁ : Tensor α) (C : Tensor α) :
    reindexTensor e C ∈ closure (allFiniteLaminates (reindexTensor e L₀) (reindexTensor e L₁)) ↔
      C ∈ closure (allFiniteLaminates L₀ L₁) := by
  constructor
  · intro h
    have h' := laminateClosure_reindex e.symm (reindexTensor e L₀) (reindexTensor e L₁) h
    simpa only [reindexTensor_symm_left] using h'
  · exact laminateClosure_reindex e L₀ L₁

theorem laminationClosureAt_reindex {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (L₀ L₁ : Tensor α) (θ : ℝ) {C : Tensor α}
    (hC : C ∈ laminationClosureAt L₀ L₁ θ) :
    reindexTensor e C ∈ laminationClosureAt (reindexTensor e L₀) (reindexTensor e L₁) θ := by
  have hclosed : IsClosed {C : Tensor α | reindexTensor e C ∈
      laminationClosureAt (reindexTensor e L₀) (reindexTensor e L₁) θ} :=
    isClosed_closure.preimage (reindexTensor_continuous e)
  apply closure_minimal (fun B hB => ?_) hclosed hC
  exact subset_closure (finiteLaminateAt_reindex e hB)

end HierarchicalLaminates.GClosure
