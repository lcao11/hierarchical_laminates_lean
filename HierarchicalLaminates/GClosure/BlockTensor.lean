module

public import HierarchicalLaminates.GClosure.Interfaces

/-! Appending the same uncoupled quadratic energy in extra potential components. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open Matrix HierarchicalLaminates.Lamination

variable {α β : Type*}

def leftGradient (F : Gradient (α ⊕ β)) : Gradient α := fun p => F (p.1, .inl p.2)

def rightGradient (F : Gradient (α ⊕ β)) : Gradient β := fun p => F (p.1, .inr p.2)

def joinGradient (F : Gradient α) (G : Gradient β) : Gradient (α ⊕ β) := fun p =>
  match p.2 with
  | .inl a => F (p.1, a)
  | .inr b => G (p.1, b)

@[simp] theorem left_joinGradient (F : Gradient α) (G : Gradient β) :
    leftGradient (joinGradient F G) = F := rfl

@[simp] theorem right_joinGradient (F : Gradient α) (G : Gradient β) :
    rightGradient (joinGradient F G) = G := rfl

theorem join_left_right (F : Gradient (α ⊕ β)) :
    joinGradient (leftGradient F) (rightGradient F) = F := by
  ext ⟨i, a⟩
  cases a <;> rfl

def extendTensor (C : Tensor α) : Tensor (α ⊕ β) := by
  classical
  exact fun p q => match p.2, q.2 with
    | .inl a, .inl b => C (p.1, a) (q.1, b)
    | .inr a, .inr b => if p.1 = q.1 ∧ a = b then 1 else 0
    | _, _ => 0

@[simp] theorem extendTensor_inl_inl (C : Tensor α) (i j : Fin 2) (a b : α) :
    extendTensor (β := β) C (i, .inl a) (j, .inl b) = C (i,a) (j,b) := rfl

@[simp] theorem extendTensor_inl_inr (C : Tensor α) (i j : Fin 2) (a : α) (b : β) :
    extendTensor C (i, .inl a) (j, .inr b) = 0 := rfl

@[simp] theorem extendTensor_inr_inl (C : Tensor α) (i j : Fin 2) (a : β) (b : α) :
    extendTensor C (i, .inr a) (j, .inl b) = 0 := rfl

@[simp] theorem extendTensor_inr_inr [DecidableEq β] (C : Tensor α) (i j : Fin 2) (a b : β) :
    extendTensor C (i, .inr a) (j, .inr b) = if i = j ∧ a = b then 1 else 0 := by
  classical
  by_cases h : i = j ∧ a = b <;> simp [extendTensor, h]

variable [Fintype α] [Fintype β]

theorem sum_spatial_sum (f : Fin 2 × (α ⊕ β) → ℝ) :
    (∑ p, f p) = (∑ p : Fin 2 × α, f (p.1, .inl p.2)) +
      ∑ p : Fin 2 × β, f (p.1, .inr p.2) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_sum_type, Finset.sum_add_distrib]

theorem extendTensor_mulVec_inl (C : Tensor α) (F : Gradient (α ⊕ β))
    (i : Fin 2) (a : α) :
    (extendTensor C *ᵥ F) (i, .inl a) = (C *ᵥ leftGradient F) (i,a) := by
  classical
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fintype.sum_sum_type,
    extendTensor, leftGradient]

theorem extendTensor_mulVec_inr (C : Tensor α) (F : Gradient (α ⊕ β))
    (i : Fin 2) (a : β) : (extendTensor C *ᵥ F) (i, .inr a) = F (i, .inr a) := by
  classical
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fintype.sum_sum_type,
      extendTensor, eq_comm]

theorem quadraticEnergy_extendTensor (C : Tensor α) (F : Gradient (α ⊕ β)) :
    quadraticEnergy (extendTensor C) F = quadraticEnergy C (leftGradient F) +
      ∑ p : Fin 2 × β, (rightGradient F p) ^ 2 := by
  unfold quadraticEnergy dotProduct
  rw [sum_spatial_sum]
  simp only [extendTensor_mulVec_inl, extendTensor_mulVec_inr]
  simp only [leftGradient, rightGradient, pow_two]

omit [Fintype α] [Fintype β] in
theorem extendTensor_isHermitian {C : Tensor α} (hC : C.IsHermitian) :
    (extendTensor (β := β) C).IsHermitian := by
  classical
  ext ⟨i,a⟩ ⟨j,b⟩
  cases a <;> cases b
  · simpa using hC.apply (i, _) (j, _)
  · simp [extendTensor]
  · simp [extendTensor]
  · simp [extendTensor, and_comm, eq_comm]

theorem extendTensor_posDef {C : Tensor α} (hC : C.PosDef) :
    (extendTensor (β := β) C).PosDef := by
  classical
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (extendTensor_isHermitian hC.isHermitian)
  intro F hF
  change 0 < quadraticEnergy (extendTensor C) F
  rw [quadraticEnergy_extendTensor]
  have hsum : 0 ≤ ∑ p : Fin 2 × β, (rightGradient F p) ^ 2 :=
    Finset.sum_nonneg (fun p _ => sq_nonneg _)
  by_cases hleft : leftGradient F = 0
  · have hright : rightGradient F ≠ 0 := by
      intro hz
      apply hF
      rw [← join_left_right F, hleft, hz]
      ext ⟨i,a⟩
      cases a <;> rfl
    have hp : ∃ p, rightGradient F p ≠ 0 := Function.ne_iff.mp hright
    obtain ⟨p,hp⟩ := hp
    have hs : 0 < ∑ q : Fin 2 × β, (rightGradient F q) ^ 2 :=
      Finset.sum_pos' (fun q _ => sq_nonneg _) ⟨p, Finset.mem_univ _, sq_pos_of_ne_zero hp⟩
    simpa [hleft, quadraticEnergy] using hs
  · have hp := hC.dotProduct_mulVec_pos hleft
    exact add_pos_of_pos_of_nonneg hp hsum

theorem extendTensor_continuous : Continuous (fun C : Tensor α => extendTensor (β := β) C) := by
  apply continuous_pi
  rintro ⟨i,a⟩
  apply continuous_pi
  rintro ⟨j,b⟩
  cases a <;> cases b
  · change Continuous (fun C : Tensor α => C (i,_) (j,_))
    fun_prop
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const

theorem extendTensor_sub_posSemidef {A B : Tensor α} (h : (B-A).PosSemidef) :
    (extendTensor (β := β) B - extendTensor A).PosSemidef := by
  classical
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    rintro ⟨i,a⟩ ⟨j,b⟩
    cases a <;> cases b
    · simpa [Matrix.sub_apply] using h.isHermitian.apply (i,_) (j,_)
    · simp [extendTensor]
    · simp [extendTensor]
    · simp [extendTensor]
  · intro F
    simp only [star_trivial]
    change 0 ≤ quadraticEnergy (extendTensor B - extendTensor A) F
    have heq : quadraticEnergy (extendTensor B - extendTensor A) F =
        quadraticEnergy B (leftGradient F) - quadraticEnergy A (leftGradient F) := by
      change F ⬝ᵥ (extendTensor B - extendTensor A) *ᵥ F = _
      rw [Matrix.sub_mulVec, dotProduct_sub]
      change quadraticEnergy (extendTensor B) F - quadraticEnergy (extendTensor A) F = _
      rw [quadraticEnergy_extendTensor, quadraticEnergy_extendTensor]
      ring
    rw [heq]
    have hp := h.dotProduct_mulVec_nonneg (leftGradient F)
    simpa [quadraticEnergy, Matrix.sub_mulVec, dotProduct_sub] using hp
end HierarchicalLaminates.GClosure
