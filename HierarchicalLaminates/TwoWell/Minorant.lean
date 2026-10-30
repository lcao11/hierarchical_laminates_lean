module

public import HierarchicalLaminates.TwoWell.DualLamination
public import HierarchicalLaminates.TwoWell.MinorantRegularity
public import HierarchicalLaminates.Lamination.LayerTrial

/-!
# The rank-one convex minorant and its separating lower bound

The proof has three steps: choose minimizers at the
two compatible gradients; laminate their tensors and planar duals; then
apply the same layer-trial inequality to both energy blocks.

The all-flux lower bound is the family's loading equality followed by a
completed square, valid for every tensor in the family and every mean flux.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.TwoWell

open Matrix HierarchicalLaminates HierarchicalLaminates.Lamination HierarchicalLaminates.Material

/-- Both blocks share the same arbitrary interface normal and layer fraction. -/
theorem minorant_rankOneConvex : RankOneConvex minorant := by
  intro F₁ F₂ hcompat a
  obtain ⟨n, z₁, z₂, hjump₁, hjump₂⟩ := hcompat
  obtain ⟨A, hA, hminA⟩ := minorant_attained F₁
  obtain ⟨B, hB, hminB⟩ := minorant_attained F₂
  let D := computedLayerTensor A B n (a : ℝ)
  have hLayer : IsLayerTensor A B n a D :=
    computedLayerTensor_represents_minimum (family_posDef hA) (family_posDef hB) n a
  have hD : D ∈ materialFamily rho :=
    materialFamily_stable rho_pos.le rho_lt_two_thirds hA hB n a hLayer
  have hDual := dual_isLayerTensor (family_posDef hA) (family_posDef hB)
    (family_posDef hD) n a hLayer
  let F := (a : ℝ) • F₁ + (1 - (a : ℝ)) • F₂
  have hprimal := hLayer.energy_le_of_compatible z₁ hjump₁
  have hcomplementary := hDual.energy_le_of_compatible z₂ hjump₂
  calc
    minorant F ≤ pairedEnergy D F := minorant_le_pairedEnergy hD F
    _ ≤ (a : ℝ) * pairedEnergy A F₁ + (1 - (a : ℝ)) * pairedEnergy B F₂ := by
      unfold pairedEnergy
      change quadraticEnergy D ((a : ℝ) • F₁.1 + (1 - (a : ℝ)) • F₂.1) +
        quadraticEnergy (dual D) ((a : ℝ) • F₁.2 + (1 - (a : ℝ)) • F₂.2) ≤ _
      linarith
    _ = (a : ℝ) * minorant F₁ + (1 - (a : ℝ)) * minorant F₂ := by
      rw [hminA, hminB]

/-- The family's equal loading energies give the completed-square identity. -/
theorem family_pairedEnergy_completed_square {A : Tensor16} (hA : A ∈ materialFamily rho)
    (p : Gradient16) :
    pairedEnergy A (xiFlat, rotate p) = 2 * (etaFlat ⬝ᵥ p) +
      quadraticEnergy A⁻¹ (p - A *ᵥ etaFlat) := by
  have hpos := family_posDef hA
  let := hpos.isUnit.invertible
  have hbalance : quadraticEnergy A etaFlat = quadraticEnergy A xiFlat := by
    have h := materialFamily_loading_balance hA
    unfold loadingDifference at h
    linarith
  have hsquare := complete_square hpos.inv etaFlat p
  rw [Matrix.inv_inv_of_invertible] at hsquare
  change quadraticEnergy A⁻¹ p - 2 * (p ⬝ᵥ etaFlat) =
    quadraticEnergy A⁻¹ (p - A *ᵥ etaFlat) - quadraticEnergy A etaFlat at hsquare
  change quadraticEnergy A xiFlat + quadraticEnergy (dual A) (rotate p) = _
  rw [dual_quadratic_rotate]
  rw [dotProduct_comm p etaFlat] at hsquare
  linarith

/-- The completed square is nonnegative for every mean flux. -/
theorem minorant_lower_bound (p : Gradient16) :
    2 * (etaFlat ⬝ᵥ p) ≤ minorant (xiFlat, rotate p) := by
  apply le_minorant
  intro A hA
  rw [family_pairedEnergy_completed_square hA p]
  have hnonnegative : 0 ≤ quadraticEnergy A⁻¹ (p - A *ᵥ etaFlat) :=
    (family_posDef hA).inv.posSemidef.dotProduct_mulVec_nonneg _
  linarith

end HierarchicalLaminates.TwoWell
