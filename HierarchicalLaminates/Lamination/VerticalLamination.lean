module

public import HierarchicalLaminates.Lamination.ConstitutiveFamily
public import HierarchicalLaminates.Lamination.ParameterStability

/-!
# The vertical-normal case of the physical lamination formula
-/

@[expose] public section

namespace HierarchicalLaminates.Lamination

open Matrix

noncomputable section

theorem jumpSourceMatrix_material_vertical (H₁ H₂ : RMatrix8) (n : LayerNormal)
    (hn : n.coordinates 0 = 0) :
    jumpSourceMatrix (materialTensor H₁) (materialTensor H₂) n = 0 := by
  ext a ⟨i, b⟩
  fin_cases i <;>
    simp [jumpSourceMatrix, normalMatrix, materialTensor, Matrix.mul_apply,
      Matrix.transpose_apply, Fintype.sum_prod_type, Fin.sum_univ_two, hn]

theorem computedLayerTensor_material_vertical (H₁ H₂ : RMatrix8) (n : LayerNormal)
    (hn : n.coordinates 0 = 0) (weight : ℝ) :
    computedLayerTensor (materialTensor H₁) (materialTensor H₂) n weight =
      materialTensor (matrixAverage weight H₁ H₂) := by
  rw [computedLayerTensor, jumpSourceMatrix_material_vertical H₁ H₂ n hn]
  simp only [Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, smul_zero, sub_zero]
  exact materialTensor_average H₁ H₂ weight

theorem materialFamily_vertical_stable {ρ : ℝ} (hρ : 0 ≤ ρ) (hρlt : ρ < 2 / 3)
    {C₁ C₂ C : Tensor (Fin 16)} (h₁ : C₁ ∈ materialFamily ρ)
    (h₂ : C₂ ∈ materialFamily ρ) (n : LayerNormal) (hn : n.coordinates 0 = 0)
    (weight : LayerProportion) (hlayer : IsLayerTensor C₁ C₂ n weight C) :
    C ∈ materialFamily ρ := by
  have hpos₁ := materialFamily_posDef hρ hρlt h₁
  have hpos₂ := materialFamily_posDef hρ hρlt h₂
  rcases h₁ with ⟨H₁, hmem₁, hlow₁, hupp₁, rfl⟩
  rcases h₂ with ⟨H₂, hmem₂, hlow₂, hupp₂, rfl⟩
  have hcanonical := computedLayerTensor_represents_minimum hpos₁ hpos₂ n weight
  have heq := (hlayer.unique hcanonical).trans
    (computedLayerTensor_material_vertical H₁ H₂ n hn (weight : ℝ))
  rw [heq]
  refine ⟨matrixAverage (weight : ℝ) H₁ H₂, ?_, ?_, ?_, rfl⟩
  · exact parameterSpace.add_mem (parameterSpace.smul_mem (weight : ℝ) hmem₁)
      (parameterSpace.smul_mem (1 - (weight : ℝ)) hmem₂)
  · exact average_posSemidef weight.property.1 weight.property.2 hlow₁ hlow₂
  · exact average_upper_bound weight.property.1 weight.property.2 hupp₁ hupp₂

end

end HierarchicalLaminates.Lamination
