module

public import HierarchicalLaminates.Homogenization.FractionAlgebra
public import HierarchicalLaminates.Homogenization.EffectiveBlocks

/-!
# Arithmetic averaging for horizontal layers

Positive-definite tensors with common vertical rows have zero jump source
for horizontal layers, so their arithmetic average represents the layer
minimum.
-/

@[expose] public section
noncomputable section

namespace HierarchicalLaminates.Homogenization

open Matrix HierarchicalLaminates HierarchicalLaminates.Lamination

def verticalNormal : LayerNormal where
  coordinates := ![0, 1]
  unit_length := by norm_num

def CommonVerticalRows (B : Tensor (Fin 16)) : Prop :=
  ∀ a (i : Fin 2) b, B (1, a) (i, b) = if i = 1 then verticalR a b else 0

theorem normalMatrix_transpose_mul_vertical (B : Tensor (Fin 16)) :
    (normalMatrix verticalNormal)ᵀ * B = fun a j => B (1, a) j := by
  ext a ⟨i, b⟩
  change (∑ c : Fin 2 × Fin 16,
    normalMatrix verticalNormal c a * B c (i, b)) = B (1, a) (i, b)
  simp [normalMatrix, verticalNormal, Fintype.sum_prod_type, Fin.sum_univ_two, Pi.single_apply]

theorem jumpSourceMatrix_common_vertical {B C : Tensor (Fin 16)}
    (hB : CommonVerticalRows B) (hC : CommonVerticalRows C) :
    jumpSourceMatrix B C verticalNormal = 0 := by
  unfold jumpSourceMatrix
  erw [normalMatrix_transpose_mul_vertical (C - B)]
  ext a ⟨i, b⟩
  change C (1, a) (i, b) - B (1, a) (i, b) = 0
  rw [hB a i b, hC a i b, sub_self]

theorem computedLayerTensor_common_vertical {B C : Tensor (Fin 16)}
    (hB : CommonVerticalRows B) (hC : CommonVerticalRows C) (t : ℝ) :
    computedLayerTensor B C verticalNormal t = matrixAverage t B C := by
  rw [computedLayerTensor, jumpSourceMatrix_common_vertical hB hC]
  simp

theorem arithmeticLayer_represents_minimum {B C : Tensor (Fin 16)}
    (hBpos : B.PosDef) (hCpos : C.PosDef)
    (hB : CommonVerticalRows B) (hC : CommonVerticalRows C) (t : LayerProportion) :
    IsLayerTensor B C verticalNormal t (matrixAverage (t : ℝ) B C) := by
  have h := computedLayerTensor_represents_minimum hBpos hCpos verticalNormal t
  rwa [computedLayerTensor_common_vertical hB hC] at h

theorem materialTensor_common_vertical (H : RMatrix8) :
    CommonVerticalRows (materialTensor H) := by
  intro a i b
  fin_cases i <;> simp [materialTensor]

theorem pureTensor_common_vertical (θ : ℝ) : CommonVerticalRows (pureTensor θ) := by
  unfold pureTensor
  split_ifs
  · exact materialTensor_common_vertical 0
  · exact materialTensor_common_vertical _

theorem pureTensor_posDef (θ : ℝ) : (pureTensor θ).PosDef := by
  unfold pureTensor
  split_ifs
  · exact materialFamily_posDef rho_pos.le rho_lt_two_thirds
      (phaseZero_mem_materialFamily rho_pos.le)
  · exact materialFamily_posDef rho_pos.le rho_lt_two_thirds
      (phaseOne_mem_materialFamily rho_pos.le)

def thetaLayerProportion (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) : LayerProportion :=
  ⟨layerFraction θ, layerFraction_mem hθ₀ hθ₁⟩

theorem arithmeticCandidate_isLayerTensor {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    {B : Tensor (Fin 16)} (hBpos : B.PosDef) (hB : CommonVerticalRows B) :
    IsLayerTensor B (pureTensor θ) verticalNormal (thetaLayerProportion θ hθ₀ hθ₁)
      (arithmeticCandidate θ B) :=
  arithmeticLayer_represents_minimum hBpos (pureTensor_posDef θ) hB
    (pureTensor_common_vertical θ) (thetaLayerProportion θ hθ₀ hθ₁)

theorem arithmeticCandidate_posDef {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    {B : Tensor (Fin 16)} (hBpos : B.PosDef) : (arithmeticCandidate θ B).PosDef :=
  average_posDef (layerFraction_mem hθ₀ hθ₁).1 (layerFraction_mem hθ₀ hθ₁).2
    hBpos (pureTensor_posDef θ)

theorem arithmeticCandidate_common_vertical (θ : ℝ) {B : Tensor (Fin 16)}
    (hB : CommonVerticalRows B) : CommonVerticalRows (arithmeticCandidate θ B) := by
  intro a i b
  change layerFraction θ * B (1, a) (i, b) +
    (1 - layerFraction θ) * pureTensor θ (1, a) (i, b) = _
  rw [hB a i b, pureTensor_common_vertical θ a i b]
  ring

theorem effective_arithmeticCandidate_isLayerTensor (b : HierarchicalLaminates.Material.PhaseFraction)
    {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    IsLayerTensor (HierarchicalLaminates.Material.effectiveMatrix b) (pureTensor θ) verticalNormal
      (thetaLayerProportion θ hθ₀ hθ₁)
      (arithmeticCandidate θ (HierarchicalLaminates.Material.effectiveMatrix b)) :=
  arithmeticCandidate_isLayerTensor hθ₀ hθ₁ (effectiveMatrix_posDef b)
    (effectiveMatrix_commonVerticalRows b)

/-- A single half-fraction witness supplies a positive arithmetic layer
candidate at every prescribed fraction strictly between zero and one. -/
theorem exists_same_half_witness_for_all_candidates :
    ∃ N : ℕ, 2 ≤ N ∧
      (∫ q, HierarchicalLaminates.Binary.binaryIndicator N q ∂HierarchicalLaminates.Periodic.domainMeasure) = 1 / 2 ∧
      ∀ θ : ℝ, ∀ hθ₀ : 0 < θ, ∀ hθ₁ : θ < 1,
        IsLayerTensor (HierarchicalLaminates.Material.effectiveMatrix (HierarchicalLaminates.Material.binaryFraction N))
          (pureTensor θ) verticalNormal (thetaLayerProportion θ hθ₀ hθ₁)
          (arithmeticCandidate θ
            (HierarchicalLaminates.Material.effectiveMatrix (HierarchicalLaminates.Material.binaryFraction N))) ∧
        0 < loadingDifference xiFlat etaFlat (arithmeticCandidate θ
          (HierarchicalLaminates.Material.effectiveMatrix (HierarchicalLaminates.Material.binaryFraction N))) ∧
        arithmeticCandidate θ
            (HierarchicalLaminates.Material.effectiveMatrix (HierarchicalLaminates.Material.binaryFraction N)) ∉
          closure (allFiniteLaminates phaseZero (phaseOne rho)) := by
  obtain ⟨N, hN, _hbool, hmean, _henergy, hgap, _hnot⟩ := half_fraction_counterexample
  refine ⟨N, hN, hmean, ?_⟩
  intro θ hθ₀ hθ₁
  exact ⟨effective_arithmeticCandidate_isLayerTensor _ hθ₀ hθ₁,
    arithmeticCandidate_positive hθ₀ hθ₁ hgap,
    arithmeticCandidate_not_in_laminateClosure hθ₀ hθ₁ hgap⟩

end HierarchicalLaminates.Homogenization
