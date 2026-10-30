module

public import HierarchicalLaminates.GClosure.GenericPeriodic

/-!
# Reindexing weak potentials and cell energies by a finite-index equivalence
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material HierarchicalLaminates.Lamination

def componentEquiv {α β : Type*} (e : α ≃ β) : ComponentIndex α ≃ ComponentIndex β :=
  Equiv.prodCongr (Equiv.refl (Fin 2)) e

def reindexGradient {α β : Type*} (e : α ≃ β) (F : Gradient α) : Gradient β :=
  fun c => F ((componentEquiv e).symm c)

def reindexTensor {α β : Type*} (e : α ≃ β) (C : Tensor α) : Tensor β :=
  fun c d => C ((componentEquiv e).symm c) ((componentEquiv e).symm d)

theorem reindexTensor_isHermitian {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) {C : Tensor α} (hC : C.IsHermitian) : (reindexTensor e C).IsHermitian := by
  ext c d
  exact hC.apply ((componentEquiv e).symm c) ((componentEquiv e).symm d)

theorem reindexTensor_continuous {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) : Continuous (reindexTensor e) := by
  apply continuous_pi
  intro c
  apply continuous_pi
  intro d
  exact (continuous_apply ((componentEquiv e).symm d)).comp
    (continuous_apply ((componentEquiv e).symm c))

theorem quadraticEnergy_reindex {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (C : Tensor α) (F : Gradient α) :
    quadraticEnergy (reindexTensor e C) (reindexGradient e F) = quadraticEnergy C F := by
  unfold quadraticEnergy Matrix.mulVec dotProduct
  apply Fintype.sum_equiv (componentEquiv e).symm
  intro c
  congr 1
  apply Fintype.sum_equiv (componentEquiv e).symm
  intro d
  rfl

theorem reindexGradient_symm {α β : Type*} (e : α ≃ β) (F : Gradient β) :
    reindexGradient e (reindexGradient e.symm F) = F := by
  funext c
  rcases c with ⟨i,a⟩
  simp [reindexGradient, componentEquiv]

theorem WeakPotential.restrict_inverse {α β : Type*} (e : α ≃ β) (u : WeakPotential β) :
    (u.restrict e).restrict e.symm = u := by
  apply WeakPotential.ext
  · funext a
    simp [WeakPotential.restrict]
  · funext c
    simp [WeakPotential.restrict]

theorem genericFieldEnergy_reindex {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (L₀ L₁ : Tensor α) (b : PhaseFraction) (F : Gradient α)
    (u : WeakPotential α) :
    genericFieldEnergy (reindexTensor e L₀) (reindexTensor e L₁) b
      (reindexGradient e F) (u.restrict e.symm) = genericFieldEnergy L₀ L₁ b F u := by
  unfold genericFieldEnergy
  apply Fintype.sum_equiv (componentEquiv e).symm
  intro c
  apply Fintype.sum_equiv (componentEquiv e).symm
  intro d
  rfl

theorem genericCellEnergy_reindex {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (L₀ L₁ : Tensor α) (b : PhaseFraction) (F : Gradient α) :
    genericCellEnergy (reindexTensor e L₀) (reindexTensor e L₁) b
      (reindexGradient e F) = genericCellEnergy L₀ L₁ b F := by
  unfold genericCellEnergy
  apply congrArg sInf
  ext E
  constructor
  · rintro ⟨v,rfl⟩
    refine ⟨v.restrict e, ?_⟩
    have h := genericFieldEnergy_reindex e L₀ L₁ b F (v.restrict e)
    rw [WeakPotential.restrict_inverse] at h
    exact h.symm
  · rintro ⟨u,rfl⟩
    exact ⟨u.restrict e.symm, genericFieldEnergy_reindex e L₀ L₁ b F u⟩

end HierarchicalLaminates.GClosure
