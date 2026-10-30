module

public import HierarchicalLaminates.TwoWell.MaterialCompactness
public import HierarchicalLaminates.TwoWell.Rotation

/-! Continuity and homogeneity of the compact-family energy minimum. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.TwoWell

open Matrix HierarchicalLaminates HierarchicalLaminates.Lamination

theorem family_pairedEnergy_image (F : PairedGradient) :
    (fun A : FamilyTensor => pairedEnergy (A : Tensor16) F) '' Set.univ =
      (fun A : Tensor16 => pairedEnergy A F) '' materialFamily rho := by
  ext E
  constructor
  · rintro ⟨A,_,rfl⟩
    exact ⟨A,A.property,rfl⟩
  · rintro ⟨A,hA,rfl⟩
    exact ⟨⟨A,hA⟩,Set.mem_univ _,rfl⟩

theorem minorant_continuous : Continuous minorant := by
  change Continuous (fun F : PairedGradient =>
    sInf ((fun A : Tensor16 => pairedEnergy A F) '' materialFamily rho))
  have h := (isCompact_univ : IsCompact (Set.univ : Set FamilyTensor)).continuous_sInf
    (f := fun (F : PairedGradient) (A : FamilyTensor) => pairedEnergy (A : Tensor16) F)
    family_pairedEnergy_joint_continuous
  simpa only [family_pairedEnergy_image] using h

theorem minorant_homogeneous (r : ℝ) (F : PairedGradient) :
    minorant (r • F) = r^2 * minorant F := by
  apply le_antisymm
  · obtain ⟨A,hA,heq⟩ := minorant_attained F
    calc
      minorant (r • F) ≤ pairedEnergy A (r • F) := minorant_le_pairedEnergy hA _
      _ = r^2 * minorant F := by rw [pairedEnergy_homogeneous, heq]
  · obtain ⟨A,hA,heq⟩ := minorant_attained (r • F)
    calc
      r^2 * minorant F ≤ r^2 * pairedEnergy A F :=
        mul_le_mul_of_nonneg_left (minorant_le_pairedEnergy hA F) (sq_nonneg r)
      _ = minorant (r • F) := by rw [heq, pairedEnergy_homogeneous]

theorem minorant_nonneg (F : PairedGradient) : 0 ≤ minorant F := by
  apply le_minorant
  intro A hA
  exact pairedEnergy_nonneg (family_posDef hA) F

theorem minorant_le_twoWellEnergy (F : PairedGradient) :
    minorant F ≤ twoWellEnergy F := by
  apply le_min
  · exact minorant_le_pairedEnergy (phaseZero_mem_materialFamily rho_pos.le) F
  · exact minorant_le_pairedEnergy (phaseOne_mem_materialFamily rho_pos.le) F

end HierarchicalLaminates.TwoWell
