module

public import HierarchicalLaminates.TwoWell.Base
public import HierarchicalLaminates.Lamination.MaterialEmbedding
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Order.Compact

/-! Compactness of the material family and attained paired-energy minima. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.TwoWell

open Matrix HierarchicalLaminates HierarchicalLaminates.Lamination

def parameterInterval : Set RMatrix8 :=
  {H | H ∈ parameterSpace ∧ H.PosSemidef ∧ (rho • (1 : RMatrix8)-H).PosSemidef}

theorem parameterInterval_isClosed : IsClosed parameterInterval := by
  change IsClosed ((parameterSpace : Set RMatrix8) ∩
    ({H : RMatrix8 | H.PosSemidef} ∩
    {H : RMatrix8 | (rho • (1 : RMatrix8)-H).PosSemidef}))
  exact parameterSpace.closed_of_finiteDimensional.inter
    (Matrix.posSemidef_is_closed.inter
      (Matrix.posSemidef_is_closed.preimage (by fun_prop)))

theorem parameterInterval_entry_bound {H : RMatrix8} (hH : H ∈ parameterInterval)
    (i j : Fin 8) : |H i j| ≤ rho := by
  have hdiag (k : Fin 8) : H k k ≤ rho := by
    have h := hH.2.2.diag_nonneg (i := k)
    simpa using h
  have hnon (k : Fin 8) : 0 ≤ H k k := hH.2.1.diag_nonneg
  by_cases hij : i = j
  · subst j
    rw [abs_of_nonneg (hnon i)]
    exact hdiag i
  · have hsym : H j i = H i j := hH.2.1.isHermitian.apply i j
    have hp := hH.2.1.dotProduct_mulVec_nonneg
      (Pi.single i (1 : ℝ)+Pi.single j 1)
    have hm := hH.2.1.dotProduct_mulVec_nonneg
      (Pi.single i (1 : ℝ)-Pi.single j 1)
    simp only [star_trivial, Matrix.mulVec_add, Matrix.mulVec_sub,
      dotProduct_add, dotProduct_sub, add_dotProduct, sub_dotProduct] at hp hm
    simp [hsym] at hp hm
    exact abs_le.mpr ⟨by linarith [hdiag i, hdiag j], by linarith [hdiag i, hdiag j]⟩

theorem parameterInterval_isCompact : IsCompact parameterInterval := by
  apply (isCompact_Icc (a := -rho) (b := rho)).matrix.of_isClosed_subset
    parameterInterval_isClosed
  intro H hH i j
  exact abs_le.mp (parameterInterval_entry_bound hH i j)

theorem materialTensor_continuous : Continuous materialTensor := by
  have heq : materialTensor = fun H : RMatrix8 =>
      phaseZero-reducedLiftMatrix*H*reducedLiftMatrixᵀ := by
    funext H
    exact materialTensor_affine H
  rw [heq]
  fun_prop

theorem materialFamily_eq_image : materialFamily rho = materialTensor '' parameterInterval := by
  ext A
  constructor
  · rintro ⟨H,hp,hl,hu,rfl⟩
    exact ⟨H,⟨hp,hl,hu⟩,rfl⟩
  · rintro ⟨H,⟨hp,hl,hu⟩,rfl⟩
    exact ⟨H,hp,hl,hu,rfl⟩

theorem materialFamily_isCompact : IsCompact (materialFamily rho) := by
  rw [materialFamily_eq_image]
  exact parameterInterval_isCompact.image materialTensor_continuous

theorem materialFamily_nonempty : (materialFamily rho).Nonempty :=
  ⟨phaseZero, phaseZero_mem_materialFamily rho_pos.le⟩

theorem family_posDef {A : Tensor16} (hA : A ∈ materialFamily rho) : A.PosDef :=
  materialFamily_posDef rho_pos.le rho_lt_two_thirds hA

abbrev FamilyTensor := {A : Tensor16 // A ∈ materialFamily rho}

instance : CompactSpace FamilyTensor :=
  isCompact_iff_compactSpace.mp materialFamily_isCompact

theorem family_inverse_continuous : Continuous (fun A : FamilyTensor => (A : Tensor16)⁻¹) := by
  apply continuous_iff_continuousAt.mpr
  intro A
  apply (continuousAt_matrix_inv (A : Tensor16) ?_).comp continuous_subtype_val.continuousAt
  simpa only [Ring.inverse_eq_inv'] using
    (continuousAt_inv₀ (family_posDef A.property).det_pos.ne')

theorem family_dual_continuous : Continuous (fun A : FamilyTensor => dual (A : Tensor16)) := by
  exact (continuous_const.mul family_inverse_continuous).mul continuous_const

theorem quadraticEnergy_continuous : Continuous (fun p : Tensor16 × Gradient16 => quadraticEnergy p.1 p.2) := by
  unfold quadraticEnergy Matrix.mulVec dotProduct
  fun_prop

theorem family_pairedEnergy_joint_continuous :
    Continuous (fun p : PairedGradient × FamilyTensor => pairedEnergy (p.2 : Tensor16) p.1) := by
  unfold pairedEnergy
  exact (quadraticEnergy_continuous.comp
    ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst.fst)).add
    (quadraticEnergy_continuous.comp
      ((family_dual_continuous.comp continuous_snd).prodMk continuous_fst.snd))

theorem pairedEnergy_continuousOn_family (F : PairedGradient) :
    ContinuousOn (fun A : Tensor16 => pairedEnergy A F) (materialFamily rho) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact family_pairedEnergy_joint_continuous.comp (continuous_const.prodMk continuous_id)

theorem minorant_attained (F : PairedGradient) :
    ∃ A ∈ materialFamily rho, minorant F = pairedEnergy A F := by
  exact materialFamily_isCompact.exists_sInf_image_eq materialFamily_nonempty
    (pairedEnergy_continuousOn_family F)

theorem minorant_le_pairedEnergy {A : Tensor16} (hA : A ∈ materialFamily rho)
    (F : PairedGradient) : minorant F ≤ pairedEnergy A F := by
  exact csInf_le (materialFamily_isCompact.image_of_continuousOn
    (pairedEnergy_continuousOn_family F)).bddBelow ⟨A,hA,rfl⟩

theorem le_minorant (F : PairedGradient) {r : ℝ}
    (h : ∀ A ∈ materialFamily rho, r ≤ pairedEnergy A F) : r ≤ minorant F := by
  obtain ⟨A,hA,heq⟩ := minorant_attained F
  rw [heq]
  exact h A hA

end HierarchicalLaminates.TwoWell
