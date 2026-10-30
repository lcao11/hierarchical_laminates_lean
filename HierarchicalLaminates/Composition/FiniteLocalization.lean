module

public import HierarchicalLaminates.Composition.LocalizationError
public import HierarchicalLaminates.Composition.ScaleSelection

/-! A common cutoff and microscopic scale for finitely many cell loadings. -/

@[expose] public section
noncomputable section

namespace HierarchicalLaminates.Composition

open HierarchicalLaminates HierarchicalLaminates.Periodic

theorem exists_common_localization {I : Type*} [Fintype I]
    (a : ℝ) (ha₀ : 0 < a) (ha : a ≤ 1) (u ψ : I → RegularPotential)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, ∃ hδ : 0 < δ, ∃ r : ℕ, ∃ hr : 0 < r, ∃ k : ℕ, 0 < k ∧
      ∀ j : I,
        ‖(localizedPotential ha₀ ha hδ hr k (u j)).field - (u j).slabField a r k‖ +
        ‖(localizedPotential ha₀ ha hδ hr k (ψ j)).field - (ψ j).slabField a r k‖ < ε := by
  classical
  let G : I → ℝ := fun j => ‖(u j).gradient‖ + ‖(ψ j).gradient‖
  let P : I → ℝ := fun j => potentialBound (u j) + potentialBound (ψ j)
  let Gsum : ℝ := ∑ j : I, G j
  let Psum : ℝ := ∑ j : I, P j
  let M : ℝ := 32 * Gsum
  have hG (j : I) : 0 ≤ G j := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hP (j : I) : 0 ≤ P j :=
    add_nonneg (potentialBound_nonneg _) (potentialBound_nonneg _)
  have hGj (j : I) : 32 * G j ≤ M := by
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun j _ => hG j) (Finset.mem_univ j)) (by norm_num)
  have hPj (j : I) : P j ≤ Psum :=
    Finset.single_le_sum (fun j _ => hP j) (Finset.mem_univ j)
  obtain ⟨δ,hδ,hδa,hwidth⟩ := exists_small_width ha₀ M (by linarith : 0 < ε/2)
  let D : ℝ := 32 * cutoffDerivativeBound a δ * Psum
  have hDj (j : I) : 32 * cutoffDerivativeBound a δ * P j ≤ D :=
    mul_le_mul_of_nonneg_left (hPj j)
      (mul_nonneg (by norm_num) (cutoffDerivativeBound_nonneg a δ))
  obtain ⟨r,k,hr,hk,hscale⟩ := exists_micro_scale ha₀ M D (by linarith : 0 < ε/2)
  refine ⟨δ,hδ,r,hr,k,hk,?_⟩
  intro j
  have hu := localizedPotential_error_bound ha₀ ha hδ (by linarith : δ < a/4) hr k (u j)
  have hψ := localizedPotential_error_bound ha₀ ha hδ (by linarith : δ < a/4) hr k (ψ j)
  calc
    _ ≤ 32 * (‖(u j).gradient‖ * Real.sqrt (4*δ) +
          |(k : ℝ)/(a*r)-1| * ‖(u j).gradient‖ +
          (r : ℝ)⁻¹ * cutoffDerivativeBound a δ * potentialBound (u j)) +
        32 * (‖(ψ j).gradient‖ * Real.sqrt (4*δ) +
          |(k : ℝ)/(a*r)-1| * ‖(ψ j).gradient‖ +
          (r : ℝ)⁻¹ * cutoffDerivativeBound a δ * potentialBound (ψ j)) := add_le_add hu hψ
    _ = (32 * G j) * Real.sqrt (4*δ) +
        (32 * G j) * |(k : ℝ)/(a*r)-1| +
        (r : ℝ)⁻¹ * (32 * cutoffDerivativeBound a δ * P j) := by
      dsimp [G,P]
      ring
    _ ≤ M * Real.sqrt (4*δ) + M * |(k : ℝ)/(a*r)-1| + (r : ℝ)⁻¹ * D := by
      apply add_le_add
      · exact add_le_add
          (mul_le_mul_of_nonneg_right (hGj j) (Real.sqrt_nonneg _))
          (mul_le_mul_of_nonneg_right (hGj j) (abs_nonneg _))
      · exact mul_le_mul_of_nonneg_left (hDj j) (inv_nonneg.mpr (Nat.cast_nonneg r))
    _ < ε := by linarith

end HierarchicalLaminates.Composition
