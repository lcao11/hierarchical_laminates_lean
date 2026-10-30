module
public import HierarchicalLaminates.GClosure.BlockTensor
public import HierarchicalLaminates.GClosure.FractionHierarchy
/-! Lamination with an identical uncoupled identity block. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace HierarchicalLaminates.GClosure
open Matrix HierarchicalLaminates HierarchicalLaminates.Lamination
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
def leftJump (z : α ⊕ β → ℝ) : α → ℝ := fun a => z (.inl a)
def rightJump (z : α ⊕ β → ℝ) : β → ℝ := fun b => z (.inr b)
@[simp] theorem left_firstLayerField (n : LayerNormal) (a : ℝ)
    (F : Gradient (α ⊕ β)) (z : α ⊕ β → ℝ) :
    leftGradient (firstLayerField n a F z) = firstLayerField n a (leftGradient F) (leftJump z) := rfl
@[simp] theorem right_firstLayerField (n : LayerNormal) (a : ℝ)
    (F : Gradient (α ⊕ β)) (z : α ⊕ β → ℝ) :
    rightGradient (firstLayerField n a F z) = firstLayerField n a (rightGradient F) (rightJump z) := rfl
@[simp] theorem left_secondLayerField (n : LayerNormal) (a : ℝ)
    (F : Gradient (α ⊕ β)) (z : α ⊕ β → ℝ) :
    leftGradient (secondLayerField n a F z) = secondLayerField n a (leftGradient F) (leftJump z) := rfl
@[simp] theorem right_secondLayerField (n : LayerNormal) (a : ℝ)
    (F : Gradient (α ⊕ β)) (z : α ⊕ β → ℝ) :
    rightGradient (secondLayerField n a F z) = secondLayerField n a (rightGradient F) (rightJump z) := rfl
theorem identity_quadraticEnergy (F : Gradient β) :
    quadraticEnergy (1 : Tensor β) F = ∑ p, (F p)^2 := by
  classical
  simp [quadraticEnergy, dotProduct, pow_two]
theorem layerEnergy_extendTensor (B C : Tensor α) (n : LayerNormal) (a : ℝ)
    (F : Gradient (α ⊕ β)) (z : α ⊕ β → ℝ) :
    layerEnergy (extendTensor B) (extendTensor C) n a F z =
      layerEnergy B C n a (leftGradient F) (leftJump z) +
      layerEnergy (1 : Tensor β) 1 n a (rightGradient F) (rightJump z) := by
  classical
  simp only [layerEnergy, quadraticEnergy_extendTensor, left_firstLayerField,
    right_firstLayerField, left_secondLayerField, right_secondLayerField, identity_quadraticEnergy]
  ring
theorem computedLayerTensor_same (B : Tensor β) (n : LayerNormal) (a : ℝ) :
    computedLayerTensor B B n a = B := by
  classical
  have hs : jumpSourceMatrix B B n = 0 := by simp [jumpSourceMatrix]
  rw [computedLayerTensor, hs]
  simp only [Matrix.transpose_zero, Matrix.zero_mul, smul_zero, sub_zero]
  ext i j
  simp only [matrixAverage, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring
theorem identity_isLayerTensor (n : LayerNormal) (a : LayerProportion) :
    IsLayerTensor (1 : Tensor β) 1 n a 1 := by
  classical
  have h := computedLayerTensor_represents_minimum
    (Matrix.PosDef.one : (1 : Tensor β).PosDef) (Matrix.PosDef.one : (1 : Tensor β).PosDef) n a
  rwa [computedLayerTensor_same] at h
theorem layerEnergy_zeroJump (B : Tensor β) (n : LayerNormal) (a : ℝ) (F : Gradient β) :
    layerEnergy B B n a F 0 = quadraticEnergy B F := by
  have hn : normalJump n (0 : β → ℝ) = 0 := by
    ext p
    change n.coordinates p.1 * 0 = 0
    ring
  unfold layerEnergy firstLayerField secondLayerField
  rw [hn]
  simp only [smul_zero, add_zero, sub_zero]
  ring
theorem layerTensor_extend {B C D : Tensor α} {n : LayerNormal}
    {a : LayerProportion} (hD : IsLayerTensor B C n a D) :
    IsLayerTensor (extendTensor (β := β) B) (extendTensor C) n a (extendTensor D) := by
  classical
  refine ⟨extendTensor_isHermitian hD.1, ?_⟩
  intro F
  have hI := (identity_isLayerTensor (β := β) n a).2 (rightGradient F)
  constructor
  · obtain ⟨z, hz⟩ := (hD.2 (leftGradient F)).1
    refine ⟨Sum.elim z 0, ?_⟩
    rw [layerEnergy_extendTensor]
    change layerEnergy B C n (a : ℝ) (leftGradient F) z +
      layerEnergy (1 : Tensor β) 1 n (a : ℝ) (rightGradient F) 0 = _
    rw [hz, layerEnergy_zeroJump, quadraticEnergy_extendTensor, identity_quadraticEnergy]
  · rintro _ ⟨z, rfl⟩
    rw [layerEnergy_extendTensor, quadraticEnergy_extendTensor]
    have hleft := (hD.2 (leftGradient F)).2 ⟨leftJump z, rfl⟩
    have hright := hI.2 ⟨rightJump z, rfl⟩
    rw [identity_quadraticEnergy] at hright
    exact add_le_add hleft hright
theorem finiteLaminateAt_extend {L₀ L₁ C : Tensor α} {θ : ℝ}
    (h : FiniteLaminateAt L₀ L₁ θ C) :
    FiniteLaminateAt (extendTensor (β := β) L₀) (extendTensor L₁) θ (extendTensor C) := by
  induction h with
  | phaseZero => exact .phaseZero
  | phaseOne => exact .phaseOne
  | layer n w _ _ hmin ih₁ ih₂ => exact .layer n w ih₁ ih₂ (layerTensor_extend hmin)
theorem finiteLaminateAt_project_extended {L₀ L₁ : Tensor α}
    (hpos : ∀ B, FiniteLaminate L₀ L₁ B → B.PosDef) {θ : ℝ} {D : Tensor (α ⊕ β)}
    (h : FiniteLaminateAt (extendTensor L₀) (extendTensor L₁) θ D) :
    ∃ C : Tensor α, FiniteLaminateAt L₀ L₁ θ C ∧ D = extendTensor C := by
  classical
  induction h with
  | phaseZero => exact ⟨L₀, .phaseZero, rfl⟩
  | phaseOne => exact ⟨L₁, .phaseOne, rfl⟩
  | layer n w _ _ hmin ih₁ ih₂ =>
    obtain ⟨B, hB, rfl⟩ := ih₁
    obtain ⟨C, hC, rfl⟩ := ih₂
    have hc := computedLayerTensor_represents_minimum (hpos B hB.forget) (hpos C hC.forget) n w
    exact ⟨_, .layer n w hB hC hc, hmin.unique (layerTensor_extend hc)⟩
end HierarchicalLaminates.GClosure
