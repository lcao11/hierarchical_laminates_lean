module

public import HierarchicalLaminates.GClosure.DimensionClosure
public import HierarchicalLaminates.GClosure.BlockLamination

/-! The same binary witness separates the enlarged constituents for every finite set of extra components. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material HierarchicalLaminates.Lamination
  HierarchicalLaminates.Homogenization

variable {β : Type*} [Fintype β] [DecidableEq β]

def extendedXi : Gradient (Fin 16 ⊕ β) := joinGradient xiFlat 0
def extendedEta : Gradient (Fin 16 ⊕ β) := joinGradient etaFlat 0

omit [DecidableEq β] in
theorem extended_loading_difference (C : Tensor (Fin 16)) :
    loadingDifference (extendedXi (β := β)) extendedEta (extendTensor C) =
      loadingDifference xiFlat etaFlat C := by
  unfold loadingDifference
  rw [quadraticEnergy_extendTensor, quadraticEnergy_extendTensor]
  simp [extendedXi,extendedEta]

theorem original_laminate_pos (C : Tensor (Fin 16))
    (hC : FiniteLaminate phaseZero (phaseOne rho) C) : C.PosDef := by
  apply materialFamily_posDef rho_pos.le rho_lt_two_thirds
  exact finiteLaminate_mem_of_stable (phaseZero_mem_materialFamily rho_pos.le)
    (phaseOne_mem_materialFamily rho_pos.le)
    (fun n w hB hC hminimum => materialFamily_stable rho_pos.le rho_lt_two_thirds hB hC n w hminimum)
    hC

theorem extended_laminate_balance (D : Tensor (Fin 16 ⊕ β))
    (hD : FiniteLaminate (extendTensor phaseZero) (extendTensor (phaseOne rho)) D) :
    loadingDifference (extendedXi (β := β)) extendedEta D = 0 := by
  obtain ⟨θ,hθ⟩ := finiteLaminate_has_fraction hD
  obtain ⟨C,hC,rfl⟩ := finiteLaminateAt_project_extended original_laminate_pos hθ
  rw [extended_loading_difference]
  exact allFiniteLaminate_loading_balance rho_pos.le rho_lt_two_thirds hC.forget

theorem extended_laminateClosure_balance {D : Tensor (Fin 16 ⊕ β)}
    (hD : D ∈ closure (allFiniteLaminates (extendTensor phaseZero) (extendTensor (phaseOne rho)))) :
    loadingDifference (extendedXi (β := β)) extendedEta D = 0 :=
  functional_zero_on_closure (loadingDifference extendedXi extendedEta)
    (loadingDifference_continuous _ _) extended_laminate_balance hD

theorem all_extra_components_counterexample (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    ∃ b : PhaseFraction, IsBinary b ∧ phaseMean b = θ ∧
      (∀ F : Gradient (Fin 16 ⊕ β), quadraticEnergy (extendTensor (β := β) (effectiveMatrix b)) F =
        genericCellEnergy (extendTensor phaseZero) (extendTensor (phaseOne rho)) b F) ∧
      0 < loadingDifference (extendedXi (β := β)) extendedEta (extendTensor (β := β) (effectiveMatrix b)) ∧
      extendTensor (β := β) (effectiveMatrix b) ∉ closure (allFiniteLaminates
        (extendTensor phaseZero) (extendTensor (phaseOne rho))) := by
  obtain ⟨b,hb,hm,_he,hpositive,_hn⟩ :=
    HierarchicalLaminates.Composition.all_theta_counterexample θ hθ₀ hθ₁
  have hp : 0 < loadingDifference (extendedXi (β := β)) extendedEta
      (extendTensor (effectiveMatrix b)) := by
    rw [extended_loading_difference]
    exact hpositive
  refine ⟨b,hb,hm,extended_effective_energy b,hp,?_⟩
  intro hmem
  exact (ne_of_gt hp) (extended_laminateClosure_balance hmem)

theorem dimensional_inclusion_of_sixteen
    (hinclusion : ∀ θ : ℝ, laminationClosureAt phaseZero (phaseOne rho) θ ⊆ GClosure θ)
    (θ : ℝ) :
    laminationClosureAt (extendTensor (β := β) phaseZero) (extendTensor (phaseOne rho)) θ ⊆
      genericGClosure (extendTensor phaseZero) (extendTensor (phaseOne rho)) θ := by
  have hfinite : finiteLaminatesAt (extendTensor (β := β) phaseZero)
      (extendTensor (phaseOne rho)) θ ⊆
      genericGClosure (extendTensor phaseZero) (extendTensor (phaseOne rho)) θ := by
    intro D hD
    obtain ⟨C,hC,rfl⟩ := finiteLaminateAt_project_extended original_laminate_pos hD
    exact genericGClosure_extend θ (hinclusion θ (subset_closure hC))
  exact closure_minimal hfinite isClosed_closure

end HierarchicalLaminates.GClosure
