module

public import HierarchicalLaminates.TwoWell.Branches
public import HierarchicalLaminates.TwoWell.Compatibility
public import HierarchicalLaminates.GClosure.DimensionReindex

/-! Identification with spatial-first gradients of exactly thirty-two scalar potentials. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.TwoWell

open Matrix HierarchicalLaminates HierarchicalLaminates.Lamination HierarchicalLaminates.Material HierarchicalLaminates.GClosure

abbrev Gradient32 := Gradient (Fin 32)
abbrev Tensor32 := Tensor (Fin 32)

def componentSumEquiv : (Fin 16 ⊕ Fin 16) ≃ Fin 32 := finSumFinEquiv

def join32 (F : PairedGradient) : Gradient32 :=
  reindexGradient componentSumEquiv (joinSum F)

def split32 (F : Gradient32) : PairedGradient :=
  splitSum (reindexGradient componentSumEquiv.symm F)

@[simp] theorem split32_join32 (F : PairedGradient) : split32 (join32 F) = F := by
  unfold split32 join32
  have h := reindexGradient_symm componentSumEquiv.symm (joinSum F)
  simp only [Equiv.symm_symm] at h
  rw [h, splitSum_joinSum]

@[simp] theorem join32_split32 (F : Gradient32) : join32 (split32 F) = F := by
  unfold join32 split32
  rw [joinSum_splitSum, reindexGradient_symm]

theorem join32_add (F G : PairedGradient) : join32 (F + G) = join32 F + join32 G := by
  unfold join32
  rw [joinSum_add]
  rfl

theorem join32_smul (r : ℝ) (F : PairedGradient) : join32 (r • F) = r • join32 F := by
  unfold join32
  rw [joinSum_smul]
  rfl

def paired32Equiv : PairedGradient ≃ₗ[ℝ] Gradient32 where
  toFun := join32
  invFun := split32
  left_inv := split32_join32
  right_inv := join32_split32
  map_add' := join32_add
  map_smul' := join32_smul

theorem split32_add (F G : Gradient32) : split32 (F + G) = split32 F + split32 G :=
  paired32Equiv.symm.map_add F G

theorem split32_smul (r : ℝ) (F : Gradient32) : split32 (r • F) = r • split32 F :=
  paired32Equiv.symm.map_smul r F

/-- The 64 by 64 coefficient matrix acting on 2 by 32 gradients. -/
def branchTensor32 (A : Tensor16) : Tensor32 :=
  reindexTensor componentSumEquiv (pairedTensor A)

theorem branchTensor32_energy (A : Tensor16) (F : Gradient32) :
    quadraticEnergy (branchTensor32 A) F = pairedEnergy A (split32 F) := by
  have h := quadraticEnergy_reindex componentSumEquiv (pairedTensor A)
    (reindexGradient componentSumEquiv.symm F)
  rw [reindexGradient_symm] at h
  exact h.trans (pairedTensor_energy A _)

theorem branchTensor32_posDef {A : Tensor16} (hA : A.PosDef) : (branchTensor32 A).PosDef := by
  have hpaired := pairedTensor_posDef hA
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (reindexTensor_isHermitian componentSumEquiv hpaired.isHermitian)
  intro F hF
  have hnonzero : reindexGradient componentSumEquiv.symm F ≠ 0 := by
    intro hzero
    have hinverse := reindexGradient_symm componentSumEquiv F
    rw [hzero] at hinverse
    exact hF hinverse.symm
  change 0 < quadraticEnergy
    (reindexTensor componentSumEquiv (pairedTensor A)) F
  rw [← reindexGradient_symm componentSumEquiv F, quadraticEnergy_reindex]
  exact hpaired.dotProduct_mulVec_pos hnonzero

def wellZero32 (F : Gradient32) : ℝ := quadraticEnergy (branchTensor32 phaseZero) F
def wellOne32 (F : Gradient32) : ℝ := quadraticEnergy (branchTensor32 (phaseOne rho)) F
def twoWellEnergy32 (F : Gradient32) : ℝ := min (wellZero32 F) (wellOne32 F)

theorem wellZero32_eq (F : Gradient32) : wellZero32 F = wellZero (split32 F) :=
  branchTensor32_energy phaseZero F

theorem wellOne32_eq (F : Gradient32) : wellOne32 F = wellOne (split32 F) :=
  branchTensor32_energy (phaseOne rho) F

theorem twoWellEnergy32_eq (F : Gradient32) :
    twoWellEnergy32 F = twoWellEnergy (split32 F) := by
  rw [twoWellEnergy32, wellZero32_eq, wellOne32_eq]
  rfl

theorem branches32_posDef :
    (branchTensor32 phaseZero).PosDef ∧ (branchTensor32 (phaseOne rho)).PosDef := by
  exact ⟨branchTensor32_posDef (materialFamily_posDef rho_pos.le rho_lt_two_thirds
      (phaseZero_mem_materialFamily rho_pos.le)),
    branchTensor32_posDef (materialFamily_posDef rho_pos.le rho_lt_two_thirds
      (phaseOne_mem_materialFamily rho_pos.le))⟩

theorem wellZero32_homogeneous (r : ℝ) (F : Gradient32) :
    wellZero32 (r • F) = r^2*wellZero32 F := by
  simp only [wellZero32_eq, split32_smul, wellZero, pairedEnergy_homogeneous]

theorem wellOne32_homogeneous (r : ℝ) (F : Gradient32) :
    wellOne32 (r • F) = r^2*wellOne32 F := by
  simp only [wellOne32_eq, split32_smul, wellOne, pairedEnergy_homogeneous]

/-- Ordinary rank-at-most-one outer-product jumps on all thirty-two components. -/
def Compatible32 (F G : Gradient32) : Prop :=
  ∃ (n : Fin 2 → ℝ) (z : Fin 32 → ℝ), ∀ i a,
    F (i, a)-G (i, a) = n i*z a

theorem split32_left_apply (F : Gradient32) (i : Fin 2) (a : Fin 16) :
    (split32 F).1 (i, a) = F (i, componentSumEquiv (.inl a)) := rfl

theorem split32_right_apply (F : Gradient32) (i : Fin 2) (a : Fin 16) :
    (split32 F).2 (i, a) = F (i, componentSumEquiv (.inr a)) := rfl

theorem compatible32_iff (F G : Gradient32) :
    Compatible32 F G ↔ Compatible (split32 F) (split32 G) := by
  rw [compatible_iff_outerCompatible]
  constructor
  · rintro ⟨n, z, h⟩
    refine ⟨n, (fun a => z (componentSumEquiv (.inl a))),
      (fun a => z (componentSumEquiv (.inr a))), ?_, ?_⟩
    · intro i a
      exact h i (componentSumEquiv (.inl a))
    · intro i a
      exact h i (componentSumEquiv (.inr a))
  · rintro ⟨n, z₁, z₂, h₁, h₂⟩
    refine ⟨n, (fun a => Sum.elim z₁ z₂ (componentSumEquiv.symm a)), ?_⟩
    intro i a
    obtain ⟨b, rfl⟩ := componentSumEquiv.surjective a
    cases b with
    | inl b => simpa only [split32_left_apply, Equiv.symm_apply_apply, Sum.elim_inl] using h₁ i b
    | inr b => simpa only [split32_right_apply, Equiv.symm_apply_apply, Sum.elim_inr] using h₂ i b

end HierarchicalLaminates.TwoWell
