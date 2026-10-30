module

public import HierarchicalLaminates.GClosure.DimensionSixteenBridge
public import HierarchicalLaminates.GClosure.BlockTensor

/-!
# Cell-energy splitting for identical uncoupled additional components
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open MeasureTheory HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material
  HierarchicalLaminates.Lamination HierarchicalLaminates.WeakCalculus

def WeakPotential.join {α β : Type*} (u : WeakPotential α) (v : WeakPotential β) :
    WeakPotential (α ⊕ β) where
  potential := Sum.elim u.potential v.potential
  gradient c := match c.2 with
    | .inl a => u.gradient (c.1,a)
    | .inr b => v.gradient (c.1,b)
  weak := by
    intro i a test
    cases a with
    | inl a => exact u.weak i a test
    | inr a => exact v.weak i a test

theorem scalarLaw_zero_zero (b : PhaseFraction) (f : ScalarField) :
    scalarLaw 0 0 b f = 0 := by simp [scalarLaw]

theorem scalarLaw_one_one (b : PhaseFraction) (f : ScalarField) :
    scalarLaw 1 1 b f = f := by simp [scalarLaw]

theorem genericFieldEnergy_extend {α β : Type*} [Fintype α] [Fintype β]
    (L₀ L₁ : Tensor α) (b : PhaseFraction) (F : Gradient (α ⊕ β))
    (u : WeakPotential (α ⊕ β)) :
    genericFieldEnergy (extendTensor L₀) (extendTensor L₁) b F u =
      genericFieldEnergy L₀ L₁ b (leftGradient F) (u.restrict Sum.inl) +
      ∑ c : Fin 2 × β, ‖affineComponent F u (c.1, .inr c.2)‖ ^ 2 := by
  classical
  unfold genericFieldEnergy
  rw [sum_spatial_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro c _
    rw [sum_spatial_sum]
    simp only [extendTensor_inl_inl, extendTensor_inl_inr, scalarLaw_zero_zero,
      inner_zero_left, Finset.sum_const_zero, add_zero]
    rfl
  · apply Finset.sum_congr rfl
    intro c _
    rw [sum_spatial_sum]
    simp only [extendTensor_inr_inl, scalarLaw_zero_zero, inner_zero_left,
      Finset.sum_const_zero, zero_add, extendTensor_inr_inr]
    have hterm (d : Fin 2 × β) :
        inner ℝ (scalarLaw (if c.1=d.1 ∧ c.2=d.2 then 1 else 0)
          (if c.1=d.1 ∧ c.2=d.2 then 1 else 0) b
          (affineComponent F u (d.1, .inr d.2)))
          (affineComponent F u (c.1, .inr c.2)) =
        if d=c then ‖affineComponent F u (c.1, .inr c.2)‖ ^ 2 else 0 := by
      by_cases h : d=c
      · subst d
        simp [scalarLaw_one_one]
      · have h' : ¬(c.1=d.1 ∧ c.2=d.2) := by
          rintro ⟨hi,ha⟩
          exact h (Prod.ext hi.symm ha.symm)
        simp [h,h',scalarLaw_zero_zero]
    simp_rw [hterm]
    simp

theorem old_generic_energy_nonneg (b : PhaseFraction) (F : Gradient (Fin 16))
    (u : WeakPotential (Fin 16)) :
    0 ≤ genericFieldEnergy phaseZero (phaseOne rho) b F u := by
  rw [genericFieldEnergy_sixteen]
  have h := coefficientLaw_coercive b (constantField (physicalLoading F) + u.toSixteen.gradient)
  have hnonneg : 0 ≤ (1 / 4 : ℝ) *
      ‖constantField (physicalLoading F) + u.toSixteen.gradient‖ *
      ‖constantField (physicalLoading F) + u.toSixteen.gradient‖ := by positivity
  exact hnonneg.trans h

theorem old_generic_energy_bddBelow (b : PhaseFraction) (F : Gradient (Fin 16)) :
    BddBelow (Set.range (genericFieldEnergy phaseZero (phaseOne rho) b F)) :=
  ⟨0, by rintro E ⟨u,rfl⟩; exact old_generic_energy_nonneg b F u⟩

theorem genericFieldEnergy_extend_lower {β : Type*} [Fintype β]
    (b : PhaseFraction) (F : Gradient (Fin 16 ⊕ β)) (u : WeakPotential (Fin 16 ⊕ β)) :
    genericCellEnergy phaseZero (phaseOne rho) b (leftGradient F) +
      (∑ c : Fin 2 × β, (rightGradient F c)^2) ≤
      genericFieldEnergy (extendTensor phaseZero) (extendTensor (phaseOne rho)) b F u := by
  rw [genericFieldEnergy_extend]
  apply add_le_add
  · exact csInf_le (old_generic_energy_bddBelow b _) ⟨u.restrict Sum.inl, rfl⟩
  · apply Finset.sum_le_sum
    intro c _
    rw [affineComponent_norm_sq]
    exact le_add_of_nonneg_right (sq_nonneg _)

theorem genericCellEnergy_extend {β : Type*} [Fintype β]
    (b : PhaseFraction) (F : Gradient (Fin 16 ⊕ β)) :
    genericCellEnergy (extendTensor phaseZero) (extendTensor (phaseOne rho)) b F =
      genericCellEnergy phaseZero (phaseOne rho) b (leftGradient F) +
      ∑ c : Fin 2 × β, (rightGradient F c)^2 := by
  have hnonempty : (Set.range (genericFieldEnergy (extendTensor phaseZero)
      (extendTensor (phaseOne rho)) b F)).Nonempty := ⟨_, ⟨WeakPotential.zero _, rfl⟩⟩
  have hbounded : BddBelow (Set.range (genericFieldEnergy (extendTensor phaseZero)
      (extendTensor (phaseOne rho)) b F)) :=
    ⟨_, by rintro E ⟨u,rfl⟩; exact genericFieldEnergy_extend_lower b F u⟩
  apply le_antisymm
  · have hall (u : WeakPotential (Fin 16)) :
        genericCellEnergy (extendTensor phaseZero) (extendTensor (phaseOne rho)) b F -
          (∑ c : Fin 2 × β, (rightGradient F c)^2) ≤
          genericFieldEnergy phaseZero (phaseOne rho) b (leftGradient F) u := by
      have h := csInf_le hbounded (Set.mem_range_self (u.join (WeakPotential.zero β)))
      rw [genericFieldEnergy_extend] at h
      have hleft : (u.join (WeakPotential.zero β)).restrict Sum.inl = u := by
        cases u
        rfl
      rw [hleft] at h
      simp only [affineComponent, WeakPotential.join, WeakPotential.zero,
        add_zero, constantField_norm, Real.norm_eq_abs, sq_abs] at h
      change genericCellEnergy (extendTensor phaseZero) (extendTensor (phaseOne rho)) b F ≤
        genericFieldEnergy phaseZero (phaseOne rho) b (leftGradient F) u +
          ∑ c : Fin 2 × β, (rightGradient F c)^2 at h
      linarith
    have hle := le_csInf (Set.range_nonempty (genericFieldEnergy phaseZero (phaseOne rho) b
      (leftGradient F))) (by rintro E ⟨u,rfl⟩; exact hall u)
    change _ ≤ genericCellEnergy phaseZero (phaseOne rho) b (leftGradient F) at hle
    linarith
  · exact le_csInf hnonempty (by rintro E ⟨u,rfl⟩; exact genericFieldEnergy_extend_lower b F u)

theorem genericCellEnergy_extend_actual {β : Type*} [Fintype β]
    (b : PhaseFraction) (F : Gradient (Fin 16 ⊕ β)) :
    genericCellEnergy (extendTensor phaseZero) (extendTensor (phaseOne rho)) b F =
      sobolevCellEnergy (coefficientLaw b) (physicalLoading (leftGradient F)) +
      ∑ c : Fin 2 × β, (rightGradient F c)^2 := by
  rw [genericCellEnergy_extend, genericCellEnergy_sixteen]

theorem extended_effective_energy {β : Type*} [Fintype β]
    (b : PhaseFraction) (F : Gradient (Fin 16 ⊕ β)) :
    quadraticEnergy (extendTensor (effectiveMatrix b)) F =
      genericCellEnergy (extendTensor phaseZero) (extendTensor (phaseOne rho)) b F := by
  rw [genericCellEnergy_extend_actual, quadraticEnergy_extendTensor]
  congr 1
  exact effectiveMatrix_quadratic_energy b (physicalLoading (leftGradient F))

end HierarchicalLaminates.GClosure
