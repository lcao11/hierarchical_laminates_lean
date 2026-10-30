module

public import HierarchicalLaminates.Lamination.DirectionalSymbol
public import Mathlib.Tactic.FieldSimp

/-!
# Agreement between the real directional formula and the physical symbol
-/

@[expose] public section

namespace HierarchicalLaminates.Lamination

open Matrix

noncomputable section

def referenceDirectionMatrix (k : ℝ × ℝ) : Matrix (Fin 16) (Fin 16) ℝ :=
  (k.1 ^ 2) • 1 + (k.2 ^ 2) • verticalR

def referenceDirectionDiagonal (k : ℝ × ℝ) (i : Fin 16) : ℝ :=
  k.1 ^ 2 + k.2 ^ 2 * verticalDiagonalR i

def referenceDirectionInverse (k : ℝ × ℝ) : Matrix (Fin 16) (Fin 16) ℝ :=
  Matrix.diagonal fun i => (referenceDirectionDiagonal k i)⁻¹

def physicalReducedSymbol (k : ℝ × ℝ) : RMatrix8 :=
  (k.1 ^ 2) • (factorRᵀ * (referenceDirectionMatrix k)⁻¹ * factorR)

theorem referenceDirectionMatrix_diagonal (k : ℝ × ℝ) :
    referenceDirectionMatrix k = Matrix.diagonal (referenceDirectionDiagonal k) := by
  rw [referenceDirectionMatrix, verticalR_diagonal]
  ext i j
  by_cases hij : i = j <;>
    simp [referenceDirectionDiagonal, hij]

theorem referenceDirectionDiagonal_pos {k : ℝ × ℝ} (hk : k.1 ≠ 0) (i : Fin 16) :
    0 < referenceDirectionDiagonal k i := by
  have hD : 0 < verticalDiagonalR i := by
    simpa [verticalR_diagonal] using verticalR_posDef.diag_pos (i := i)
  exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hk)
    (mul_nonneg (sq_nonneg _) hD.le)

theorem referenceDirectionMatrix_inverse {k : ℝ × ℝ} (hk : k.1 ≠ 0) :
    (referenceDirectionMatrix k)⁻¹ = referenceDirectionInverse k := by
  apply Matrix.inv_eq_right_inv
  rw [referenceDirectionMatrix_diagonal]
  unfold referenceDirectionInverse
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [(referenceDirectionDiagonal_pos hk i).ne']
  · simp [hij]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem physicalReducedSymbol_eq_directionalSymbolR (k : ℝ × ℝ) :
    physicalReducedSymbol k = directionalSymbolR k := by
  by_cases hk : k.1 = 0
  · simp [physicalReducedSymbol, hk, directionalSymbolR, directionalWeightR]
  · rw [physicalReducedSymbol, referenceDirectionMatrix_inverse hk]
    have hx : 0 < k.1 ^ 2 := sq_pos_of_ne_zero hk
    have hy : 0 ≤ k.2 ^ 2 := sq_nonneg _
    have h₁ : k.1 ^ 2 + k.2 ^ 2 ≠ 0 := (add_pos_of_pos_of_nonneg hx hy).ne'
    have h₂ : 2 * k.1 ^ 2 + k.2 ^ 2 ≠ 0 := by positivity
    have h₃ : 3 * k.1 ^ 2 + k.2 ^ 2 ≠ 0 := by positivity
    have h₄ : 4 * k.1 ^ 2 + k.2 ^ 2 ≠ 0 := by positivity
    have hb₂ : k.1 ^ 2 + k.2 ^ 2 * (1 / 2) ≠ 0 := by positivity
    have hb₃ : k.1 ^ 2 + k.2 ^ 2 * (1 / 3) ≠ 0 := by positivity
    have hb₄ : k.1 ^ 2 + k.2 ^ 2 * (1 / 4) ≠ 0 := by positivity
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [referenceDirectionInverse, referenceDirectionDiagonal,
        verticalDiagonalR, directionalSymbolR, directionalWeightR, directionalDegreeR,
        factorR, gammaR, realMatrix, factorQ, gammaQ, Matrix.mul_apply,
        Matrix.transpose_apply, Matrix.diagonal_apply, Fin.sum_univ_succ] <;>
      field_simp [h₁, h₂, h₃, h₄, hb₂, hb₃, hb₄] <;> ring

end

end HierarchicalLaminates.Lamination
