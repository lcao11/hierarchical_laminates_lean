module

public import HierarchicalLaminates.Lamination.MaterialEmbedding
public import HierarchicalLaminates.Lamination.PhysicalSymbol
public import HierarchicalLaminates.Lamination.ReducedInverse
public import HierarchicalLaminates.Lamination.VerticalLamination

/-!
# Preservation of the physical family in every real direction
-/

@[expose] public section

namespace HierarchicalLaminates.Lamination

open Matrix

noncomputable section

theorem jumpStiffness_material (H₁ H₂ : RMatrix8) (n : LayerNormal) (weight : ℝ) :
    jumpStiffness (materialTensor H₁) (materialTensor H₂) n weight =
      referenceDirectionMatrix (n.coordinates 0, n.coordinates 1) -
        (n.coordinates 0 ^ 2) •
          (factorR * matrixAverage (1 - weight) H₁ H₂ * factorRᵀ) := by
  rw [jumpStiffness, materialTensor_average, normalMatrix_materialTensor]
  unfold horizontalR referenceDirectionMatrix
  simp only [smul_sub]
  abel

theorem computedLayerTensor_material_nonvertical (H₁ H₂ : RMatrix8)
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian)
    (hpos₁ : (materialTensor H₁).PosDef) (hpos₂ : (materialTensor H₂).PosDef)
    (n : LayerNormal) (hn : n.coordinates 0 ≠ 0) (weight : LayerProportion)
    (hK₁ : (directionalLambdaR (n.coordinates 0, n.coordinates 1) - H₁).PosDef)
    (hK₂ : (directionalLambdaR (n.coordinates 0, n.coordinates 1) - H₂).PosDef) :
    computedLayerTensor (materialTensor H₁) (materialTensor H₂) n (weight : ℝ) =
      materialTensor (laminateParameter
        (directionalLambdaR (n.coordinates 0, n.coordinates 1)) H₁ H₂ (weight : ℝ)) := by
  let k := (n.coordinates 0, n.coordinates 1)
  let c := n.coordinates 0 ^ 2
  let A := referenceDirectionMatrix k
  let Htilde := matrixAverage (1 - (weight : ℝ)) H₁ H₂
  let M := jumpStiffness (materialTensor H₁) (materialTensor H₂) n (weight : ℝ)
  have hA : A.PosDef := by
    change (referenceDirectionMatrix k).PosDef
    rw [referenceDirectionMatrix_diagonal]
    exact Matrix.PosDef.diagonal (referenceDirectionDiagonal_pos hn)
  have hT_eq : c • (factorRᵀ * A⁻¹ * factorR) = directionalSymbolR k :=
    physicalReducedSymbol_eq_directionalSymbolR k
  have hT : (c • (factorRᵀ * A⁻¹ * factorR)).PosDef := by
    rw [hT_eq]
    exact directionalSymbolR_posDef hn
  have hM : M.PosDef :=
    jumpStiffness_posDef hpos₁ hpos₂ n weight.property.1 weight.property.2
  have hM_eq : M = A - c • (factorR * Htilde * factorRᵀ) :=
    jumpStiffness_material H₁ H₂ n (weight : ℝ)
  have hM' : (A - c • (factorR * Htilde * factorRᵀ)).PosDef := by
    rw [← hM_eq]
    exact hM
  have hred := reduced_inverse_identity factorR A Htilde c hA hT hM'
  rw [hT_eq, ← hM_eq] at hred
  have hcalc : computedLayerTensor (materialTensor H₁) (materialTensor H₂) n
      (weight : ℝ) = materialTensor (matrixAverage (weight : ℝ) H₁ H₂ +
        ((weight : ℝ) * (1 - (weight : ℝ))) • ((H₁ - H₂) *
          (directionalLambdaR k - Htilde)⁻¹ * (H₁ - H₂))) := by
    rw [computedLayerTensor, materialTensor_average, jumpSourceMatrix_material]
    rw [materialTensor_schur_correction _ _ (hH₁.sub hH₂)]
    rw [hred]
    rfl
  rw [laminateParameter_correction _ _ _ hK₁ hK₂ weight.property.1 weight.property.2]
  exact hcalc

/-- Every variational layer of two family members belongs to the family,
for every real unit normal and proportion. -/
theorem materialFamily_stable {ρ : ℝ} (hρ : 0 ≤ ρ) (hρlt : ρ < 2 / 3)
    {C₁ C₂ C : Tensor (Fin 16)} (h₁ : C₁ ∈ materialFamily ρ)
    (h₂ : C₂ ∈ materialFamily ρ) (n : LayerNormal) (weight : LayerProportion)
    (hlayer : IsLayerTensor C₁ C₂ n weight C) : C ∈ materialFamily ρ := by
  by_cases hn : n.coordinates 0 = 0
  · exact materialFamily_vertical_stable hρ hρlt h₁ h₂ n hn weight hlayer
  · have hpos₁ := materialFamily_posDef hρ hρlt h₁
    have hpos₂ := materialFamily_posDef hρ hρlt h₂
    rcases h₁ with ⟨H₁, hmem₁, hlow₁, hupp₁, rfl⟩
    rcases h₂ with ⟨H₂, hmem₂, hlow₂, hupp₂, rfl⟩
    let k := (n.coordinates 0, n.coordinates 1)
    let Λ := directionalLambdaR k
    have hbase := directionalLambdaR_sub_contrast_posDef (k := k) hn hρlt
    have hK₁ : (Λ - H₁).PosDef := by
      have h := hbase.add_posSemidef hupp₁
      convert h using 1; abel
    have hK₂ : (Λ - H₂).PosDef := by
      have h := hbase.add_posSemidef hupp₂
      convert h using 1; abel
    have hinverse : PositiveInverseClosed parameterSpace := by
      intro H hmem hpos
      exact parameterSpace_inv_mem hmem hpos
    obtain ⟨hmem, hlower, hupper⟩ := laminateParameter_stable hinverse
      (directionalLambdaR_mem (k := k) hn) hmem₁ hmem₂
      (directionalLambdaR_posDef (k := k) hn) hbase
      hlow₁ hlow₂ hupp₁ hupp₂ weight.property.1 weight.property.2
    have hcomputed := computedLayerTensor_material_nonvertical H₁ H₂
      hlow₁.isHermitian hlow₂.isHermitian hpos₁ hpos₂ n hn weight hK₁ hK₂
    have heq := (hlayer.unique
      (computedLayerTensor_represents_minimum hpos₁ hpos₂ n weight)).trans hcomputed
    exact ⟨laminateParameter Λ H₁ H₂ (weight : ℝ), hmem, hlower, hupper, heq⟩

theorem allFiniteLaminate_loading_balance {ρ : ℝ} (hρ : 0 ≤ ρ) (hρlt : ρ < 2 / 3)
    {C : Tensor (Fin 16)} (hC : FiniteLaminate phaseZero (phaseOne ρ) C) :
    loadingDifference xiFlat etaFlat C = 0 := by
  apply materialFamily_loading_balance
  apply finiteLaminate_mem_of_stable (phaseZero_mem_materialFamily hρ)
    (phaseOne_mem_materialFamily hρ) ?_ hC
  intro C₁ C₂ C n weight h₁ h₂ hlayer
  exact materialFamily_stable hρ hρlt h₁ h₂ n weight hlayer

theorem laminateClosure_loading_balance {ρ : ℝ} (hρ : 0 ≤ ρ) (hρlt : ρ < 2 / 3)
    {C : Tensor (Fin 16)} (hC : C ∈ closure (allFiniteLaminates phaseZero (phaseOne ρ))) :
    loadingDifference xiFlat etaFlat C = 0 := by
  exact functional_zero_on_closure (loadingDifference xiFlat etaFlat)
    (loadingDifference_continuous xiFlat etaFlat)
    (fun _ h => allFiniteLaminate_loading_balance hρ hρlt h) hC

/-- A strict difference at the selected loadings separates a tensor from the
closure of all finite laminates of the two concrete phases. -/
theorem positive_loading_difference_not_in_laminateClosure {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρlt : ρ < 2 / 3) {C : Tensor (Fin 16)}
    (hgap : 0 < loadingDifference xiFlat etaFlat C) :
    C ∉ closure (allFiniteLaminates phaseZero (phaseOne ρ)) := by
  intro hC
  rw [laminateClosure_loading_balance hρ hρlt hC] at hgap
  exact lt_irrefl _ hgap

end

end HierarchicalLaminates.Lamination
