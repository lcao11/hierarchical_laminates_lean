module

public import HierarchicalLaminates.Composition.Interfaces

/-!
# Rotation of a gradient preserves its L² norm
-/

@[expose] public section
noncomputable section

namespace HierarchicalLaminates.Composition

open HierarchicalLaminates.Periodic HierarchicalLaminates.WeakCalculus

theorem curlField_norm (v : PhysicalField) : ‖curlField v‖ = ‖v‖ := by
  have heq : ‖curlField v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      physical_inner_components, physical_inner_components]
    apply Finset.sum_congr rfl
    intro a _
    simp only [Fin.sum_univ_two, curlField_component_zero, curlField_component_one,
      inner_neg_left, inner_neg_right, neg_neg]
    ring
  nlinarith [norm_nonneg (curlField v), norm_nonneg v]

theorem residual_transfer_bound (b : HierarchicalLaminates.Material.PhaseFraction)
    (e j e₀ j₀ : PhysicalField) :
    ‖j - HierarchicalLaminates.Material.coefficientLaw b e‖ ≤
      ‖j₀ - HierarchicalLaminates.Material.coefficientLaw b e₀‖ + ‖j - j₀‖ + ‖e - e₀‖ := by
  have heq : j - HierarchicalLaminates.Material.coefficientLaw b e =
      (j₀ - HierarchicalLaminates.Material.coefficientLaw b e₀) + (j - j₀) -
      HierarchicalLaminates.Material.coefficientLaw b (e - e₀) := by
    rw [map_sub]
    abel
  rw [heq]
  exact (norm_sub_le _ _).trans (add_le_add
    (norm_add_le _ _) (HierarchicalLaminates.Material.coefficientLaw_norm_le b _))

end HierarchicalLaminates.Composition
