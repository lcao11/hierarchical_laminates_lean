module

public import HierarchicalLaminates.TwoWell.Rotation
public import HierarchicalLaminates.GClosure.BlockTensor

/-! Paired quadratic tensors with one shared phase choice. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.TwoWell

open Matrix HierarchicalLaminates HierarchicalLaminates.Lamination HierarchicalLaminates.Material HierarchicalLaminates.GClosure

abbrev SumGradient := Gradient (Fin 16 ⊕ Fin 16)

def splitSum (F : SumGradient) : PairedGradient := (leftGradient F, rightGradient F)

def joinSum (F : PairedGradient) : SumGradient := joinGradient F.1 F.2

@[simp] theorem splitSum_joinSum (F : PairedGradient) : splitSum (joinSum F) = F := by
  cases F
  rfl

@[simp] theorem joinSum_splitSum (F : SumGradient) : joinSum (splitSum F) = F :=
  join_left_right F

theorem joinSum_add (F G : PairedGradient) : joinSum (F + G) = joinSum F + joinSum G := by
  ext ⟨i, a⟩
  cases a <;> rfl

theorem joinSum_smul (r : ℝ) (F : PairedGradient) : joinSum (r • F) = r • joinSum F := by
  ext ⟨i, a⟩
  cases a <;> rfl

/-- Both quadratic blocks use the same constituent A. -/
def pairedTensor (A : Tensor16) : Tensor (Fin 16 ⊕ Fin 16) := fun p q =>
  match p.2, q.2 with
  | .inl a, .inl b => A (p.1, a) (q.1, b)
  | .inr a, .inr b => dual A (p.1, a) (q.1, b)
  | _, _ => 0

theorem pairedTensor_mulVec_left (A : Tensor16) (F : SumGradient) (i : Fin 2) (a : Fin 16) :
    (pairedTensor A *ᵥ F) (i, .inl a) = (A *ᵥ leftGradient F) (i, a) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fintype.sum_sum_type,
    pairedTensor, leftGradient]

theorem pairedTensor_mulVec_right (A : Tensor16) (F : SumGradient) (i : Fin 2) (a : Fin 16) :
    (pairedTensor A *ᵥ F) (i, .inr a) = (dual A *ᵥ rightGradient F) (i, a) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fintype.sum_sum_type,
    pairedTensor, rightGradient]

theorem pairedTensor_energy (A : Tensor16) (F : SumGradient) :
    quadraticEnergy (pairedTensor A) F = pairedEnergy A (splitSum F) := by
  unfold quadraticEnergy dotProduct
  rw [sum_spatial_sum]
  simp only [pairedTensor_mulVec_left, pairedTensor_mulVec_right]
  rfl

theorem pairedTensor_isHermitian {A : Tensor16} (hA : A.PosDef) :
    (pairedTensor A).IsHermitian := by
  ext ⟨i, a⟩ ⟨j, b⟩
  cases a <;> cases b
  · exact hA.isHermitian.apply (i, _) (j, _)
  · rfl
  · rfl
  · exact (dual_posDef hA).isHermitian.apply (i, _) (j, _)

theorem pairedTensor_posDef {A : Tensor16} (hA : A.PosDef) : (pairedTensor A).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (pairedTensor_isHermitian hA)
  intro F hF
  change 0 < quadraticEnergy (pairedTensor A) F
  rw [pairedTensor_energy]
  have hl := hA.posSemidef.dotProduct_mulVec_nonneg (leftGradient F)
  have hr := (dual_posDef hA).posSemidef.dotProduct_mulVec_nonneg (rightGradient F)
  change 0 < quadraticEnergy A (leftGradient F)+quadraticEnergy (dual A) (rightGradient F)
  by_cases hz : leftGradient F = 0
  · have hn : rightGradient F ≠ 0 := by
      intro hzero
      apply hF
      rw [← join_left_right F, hz, hzero]
      ext ⟨i, a⟩
      cases a <;> rfl
    exact add_pos_of_nonneg_of_pos hl ((dual_posDef hA).dotProduct_mulVec_pos hn)
  · exact add_pos_of_pos_of_nonneg (hA.dotProduct_mulVec_pos hz) hr

end HierarchicalLaminates.TwoWell
