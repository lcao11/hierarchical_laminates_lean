module

public import HierarchicalLaminates.GClosure.DimensionCounterexample
public import HierarchicalLaminates.GClosure.DimensionLaminationReindex

/-!
# The two-phase counterexample for every number of potentials at least sixteen
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material HierarchicalLaminates.Lamination
  HierarchicalLaminates.Homogenization

def dimensionEquiv (m : ℕ) (hm : 16 ≤ m) : Fin 16 ⊕ Fin (m-16) ≃ Fin m :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hm))

def dimensionPhaseZero (m : ℕ) (hm : 16 ≤ m) : Tensor (Fin m) :=
  reindexTensor (dimensionEquiv m hm) (extendTensor (β := Fin (m-16)) phaseZero)

def dimensionPhaseOne (m : ℕ) (hm : 16 ≤ m) : Tensor (Fin m) :=
  reindexTensor (dimensionEquiv m hm) (extendTensor (β := Fin (m-16)) (phaseOne rho))

def dimensionEffective (m : ℕ) (hm : 16 ≤ m) (b : PhaseFraction) : Tensor (Fin m) :=
  reindexTensor (dimensionEquiv m hm) (extendTensor (β := Fin (m-16)) (effectiveMatrix b))

def dimensionXi (m : ℕ) (hm : 16 ≤ m) : Gradient (Fin m) :=
  reindexGradient (dimensionEquiv m hm) (extendedXi (β := Fin (m-16)))

def dimensionEta (m : ℕ) (hm : 16 ≤ m) : Gradient (Fin m) :=
  reindexGradient (dimensionEquiv m hm) (extendedEta (β := Fin (m-16)))

theorem dimensionEffective_energy (m : ℕ) (hm : 16 ≤ m) (b : PhaseFraction)
    (F : Gradient (Fin m)) :
    quadraticEnergy (dimensionEffective m hm b) F =
      genericCellEnergy (dimensionPhaseZero m hm) (dimensionPhaseOne m hm) b F := by
  unfold dimensionEffective dimensionPhaseZero dimensionPhaseOne
  rw [← reindexGradient_symm (dimensionEquiv m hm) F,
    quadraticEnergy_reindex,genericCellEnergy_reindex]
  exact extended_effective_energy b _

theorem dimensionEffective_loading_difference (m : ℕ) (hm : 16 ≤ m) (b : PhaseFraction) :
    loadingDifference (dimensionXi m hm) (dimensionEta m hm) (dimensionEffective m hm b) =
      physicalLoadingDifference b := by
  unfold loadingDifference dimensionXi dimensionEta dimensionEffective
  rw [quadraticEnergy_reindex,quadraticEnergy_reindex]
  exact extended_loading_difference (β := Fin (m-16)) (effectiveMatrix b)

theorem reindexTensor_posDef {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) {C : Tensor α} (hC : C.PosDef) : (reindexTensor e C).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (reindexTensor_isHermitian e hC.isHermitian)
  intro F hF
  have hnonzero : reindexGradient e.symm F ≠ 0 := by
    intro hz
    have he := reindexGradient_symm e F
    rw [hz] at he
    exact hF he.symm
  change 0 < quadraticEnergy (reindexTensor e C) F
  rw [← reindexGradient_symm e F,quadraticEnergy_reindex]
  exact hC.dotProduct_mulVec_pos hnonzero

theorem dimensionPhaseZero_posDef (m : ℕ) (hm : 16 ≤ m) : (dimensionPhaseZero m hm).PosDef :=
  reindexTensor_posDef _ (extendTensor_posDef
    (materialFamily_posDef rho_pos.le rho_lt_two_thirds (phaseZero_mem_materialFamily rho_pos.le)))

theorem dimensionPhaseOne_posDef (m : ℕ) (hm : 16 ≤ m) : (dimensionPhaseOne m hm).PosDef :=
  reindexTensor_posDef _ (extendTensor_posDef
    (materialFamily_posDef rho_pos.le rho_lt_two_thirds (phaseOne_mem_materialFamily rho_pos.le)))

theorem all_m_counterexample (m : ℕ) (hm : 16 ≤ m)
    (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    ∃ b : PhaseFraction, IsBinary b ∧ phaseMean b = θ ∧
      (∀ F : Gradient (Fin m), quadraticEnergy (dimensionEffective m hm b) F =
        genericCellEnergy (dimensionPhaseZero m hm) (dimensionPhaseOne m hm) b F) ∧
      0 < loadingDifference (dimensionXi m hm) (dimensionEta m hm) (dimensionEffective m hm b) ∧
      dimensionEffective m hm b ∉ closure (allFiniteLaminates
        (dimensionPhaseZero m hm) (dimensionPhaseOne m hm)) := by
  obtain ⟨b,hb,hmn,_he,hpos,hnot⟩ :=
    all_extra_components_counterexample (β := Fin (m-16)) θ hθ₀ hθ₁
  refine ⟨b,hb,hmn,dimensionEffective_energy m hm b,?_,?_⟩
  · simpa only [dimensionEffective,dimensionXi,dimensionEta,loadingDifference,
      quadraticEnergy_reindex] using hpos
  · exact fun h => hnot ((laminateClosure_reindex_iff (dimensionEquiv m hm)
      (extendTensor phaseZero) (extendTensor (phaseOne rho)) (extendTensor (effectiveMatrix b))).1 h)

end HierarchicalLaminates.GClosure
