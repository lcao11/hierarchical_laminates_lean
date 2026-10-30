module

public import HierarchicalLaminates.PaperCounterexample

/-!
# Prescribing the fraction by horizontal layering

Layering a half-fraction seed with a pure constituent gives an arithmetic
candidate at each prescribed fraction. The separating loading difference
scales by the positive proportion of the seed.
-/

@[expose] public section
noncomputable section

namespace HierarchicalLaminates.Homogenization

open HierarchicalLaminates HierarchicalLaminates.Lamination

def layerFraction (θ : ℝ) : ℝ := 2 * min θ (1 - θ)

def pureFraction (θ : ℝ) : ℝ := if θ ≤ 1 / 2 then 0 else 1

def pureTensor (θ : ℝ) : Tensor (Fin 16) :=
  if θ ≤ 1 / 2 then phaseZero else phaseOne rho

theorem layerFraction_pos {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    0 < layerFraction θ := by
  unfold layerFraction
  exact mul_pos (by norm_num) (lt_min hθ₀ (by linarith))

theorem layerFraction_le_one (θ : ℝ) : layerFraction θ ≤ 1 := by
  have h₀ := min_le_left θ (1 - θ)
  have h₁ := min_le_right θ (1 - θ)
  unfold layerFraction
  linarith

theorem layerFraction_mem {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    layerFraction θ ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨(layerFraction_pos hθ₀ hθ₁).le, layerFraction_le_one θ⟩

theorem pureFraction_values (θ : ℝ) : pureFraction θ = 0 ∨ pureFraction θ = 1 := by
  unfold pureFraction
  split_ifs <;> simp

theorem pureTensor_eq_mixtureTensor (θ : ℝ) :
    pureTensor θ = HierarchicalLaminates.Material.mixtureTensor (pureFraction θ) := by
  unfold pureTensor pureFraction
  split_ifs
  · exact HierarchicalLaminates.Material.mixtureTensor_zero.symm
  · exact HierarchicalLaminates.Material.mixtureTensor_one.symm

theorem prescribed_fraction (θ : ℝ) :
    layerFraction θ / 2 + (1 - layerFraction θ) * pureFraction θ = θ := by
  unfold layerFraction pureFraction
  split_ifs with h
  · rw [min_eq_left (by linarith : θ ≤ 1 - θ)]
    ring
  · rw [min_eq_right (by linarith : 1 - θ ≤ θ)]
    ring

theorem prescribed_fraction_mul (θ : ℝ) :
    layerFraction θ * (1 / 2) + (1 - layerFraction θ) * pureFraction θ = θ := by
  simpa only [div_eq_mul_inv, one_mul] using prescribed_fraction θ

theorem layerFraction_eq_one_iff (θ : ℝ) : layerFraction θ = 1 ↔ θ = 1 / 2 := by
  constructor
  · intro h
    have h₀ := min_le_left θ (1 - θ)
    have h₁ := min_le_right θ (1 - θ)
    unfold layerFraction at h
    linarith
  · rintro rfl
    norm_num [layerFraction]

def arithmeticCandidate (θ : ℝ) (B : Tensor (Fin 16)) : Tensor (Fin 16) :=
  matrixAverage (layerFraction θ) B (pureTensor θ)

theorem loadingDifference_average (B C : Tensor (Fin 16)) (t : ℝ) :
    loadingDifference xiFlat etaFlat (matrixAverage t B C) =
      t * loadingDifference xiFlat etaFlat B +
        (1 - t) * loadingDifference xiFlat etaFlat C := by
  unfold loadingDifference
  change quadraticFormValue (matrixAverage t B C) etaFlat -
    quadraticFormValue (matrixAverage t B C) xiFlat = _
  rw [quadratic_average, quadratic_average]
  change t * quadraticFormValue B etaFlat + (1 - t) * quadraticFormValue C etaFlat -
      (t * quadraticFormValue B xiFlat + (1 - t) * quadraticFormValue C xiFlat) =
    t * (quadraticFormValue B etaFlat - quadraticFormValue B xiFlat) +
      (1 - t) * (quadraticFormValue C etaFlat - quadraticFormValue C xiFlat)
  ring

theorem pureTensor_loading_balance (θ : ℝ) :
    loadingDifference xiFlat etaFlat (pureTensor θ) = 0 := by
  unfold pureTensor
  split_ifs
  · exact materialFamily_loading_balance (phaseZero_mem_materialFamily (le_of_lt rho_pos))
  · exact materialFamily_loading_balance (phaseOne_mem_materialFamily (le_of_lt rho_pos))

theorem arithmeticCandidate_loading_difference (θ : ℝ) (B : Tensor (Fin 16)) :
    loadingDifference xiFlat etaFlat (arithmeticCandidate θ B) =
      layerFraction θ * loadingDifference xiFlat etaFlat B := by
  rw [arithmeticCandidate, loadingDifference_average, pureTensor_loading_balance,
    mul_zero, add_zero]

theorem arithmeticCandidate_positive {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    {B : Tensor (Fin 16)} (hB : 0 < loadingDifference xiFlat etaFlat B) :
    0 < loadingDifference xiFlat etaFlat (arithmeticCandidate θ B) := by
  rw [arithmeticCandidate_loading_difference]
  exact mul_pos (layerFraction_pos hθ₀ hθ₁) hB

theorem arithmeticCandidate_not_in_laminateClosure {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    {B : Tensor (Fin 16)} (hB : 0 < loadingDifference xiFlat etaFlat B) :
    arithmeticCandidate θ B ∉ closure (allFiniteLaminates phaseZero (phaseOne rho)) :=
  positive_loading_difference_not_in_laminateClosure rho_pos.le rho_lt_two_thirds
    (arithmeticCandidate_positive hθ₀ hθ₁ hB)

end HierarchicalLaminates.Homogenization
