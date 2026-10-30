module

public import HierarchicalLaminates.Lamination.HarmonicBounds
public import Mathlib.Tactic.Module

/-!
# Noncommutative identities for the laminate harmonic mean
-/

@[expose] public section

namespace HierarchicalLaminates.Lamination

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem inverse_average_factor {A B : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (weight : ℝ) :
    matrixAverage weight A⁻¹ B⁻¹ =
      B⁻¹ * matrixAverage (1 - weight) A B * A⁻¹ := by
  let _ := hA.isUnit.invertible
  let _ := hB.isUnit.invertible
  have hscalar : 1 - (1 - weight) = weight := by ring
  simp only [matrixAverage, hscalar, mul_add, add_mul, smul_mul_assoc,
    mul_smul_comm, Matrix.mul_assoc, Matrix.inv_mul_cancel_left_of_invertible,
    Matrix.mul_inv_of_invertible, Matrix.mul_one]
  exact add_comm _ _

/-- The factors retain their noncommutative order. -/
theorem harmonicMean_product {A B : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (weight : ℝ) :
    harmonicMean weight A B = A * (matrixAverage (1 - weight) A B)⁻¹ * B := by
  let _ := hA.isUnit.invertible
  let _ := hB.isUnit.invertible
  unfold harmonicMean
  rw [inverse_average_factor hA hB weight, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  simp only [Matrix.inv_inv_of_invertible, Matrix.mul_assoc]

/-- The exact noncommutative correction identity used to turn the completed
square in the jump energy into the harmonic-mean parameter formula. -/
theorem harmonicMean_correction {A B : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.PosDef) {weight : ℝ} (hweight₀ : 0 ≤ weight) (hweight₁ : weight ≤ 1) :
    harmonicMean weight A B = matrixAverage weight A B - (weight * (1 - weight)) •
      ((A - B) * (matrixAverage (1 - weight) A B)⁻¹ * (A - B)) := by
  let K := matrixAverage (1 - weight) A B
  let Δ := A - B
  have hK : K.PosDef :=
    average_posDef (sub_nonneg.mpr hweight₁) (by linarith) hA hB
  let _ := hK.isUnit.invertible
  have hArep : A = K + weight • Δ := by
    dsimp [K, Δ, matrixAverage]
    module
  have hBrep : B = K - (1 - weight) • Δ := by
    dsimp [K, Δ, matrixAverage]
    module
  have hmean : matrixAverage weight A B = K + (2 * weight - 1) • Δ := by
    dsimp [K, Δ, matrixAverage]
    module
  rw [harmonicMean_product hA hB weight]
  change A * K⁻¹ * B = matrixAverage weight A B - (weight * (1 - weight)) • (Δ * K⁻¹ * Δ)
  calc
    A * K⁻¹ * B = (K + weight • Δ) * K⁻¹ * (K - (1 - weight) • Δ) := by
      rw [← hArep, ← hBrep]
    _ = K + (2 * weight - 1) • Δ - (weight * (1 - weight)) • (Δ * K⁻¹ * Δ) := by
      simp only [add_mul, mul_sub, smul_mul_assoc,
        mul_smul_comm, Matrix.mul_assoc,
        Matrix.mul_inv_cancel_left_of_invertible, Matrix.inv_mul_of_invertible,
        Matrix.mul_one]
      module
    _ = matrixAverage weight A B - (weight * (1 - weight)) • (Δ * K⁻¹ * Δ) := by rw [hmean]

end HierarchicalLaminates.Lamination
