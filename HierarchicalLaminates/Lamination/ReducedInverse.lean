module

public import HierarchicalLaminates.Lamination.MatrixOrder

/-!
# Reduction of the inverse in a layer jump calculation
-/

@[expose] public section

namespace HierarchicalLaminates.Lamination

open Matrix

noncomputable section

variable {a r : Type*} [Fintype a] [Fintype r] [DecidableEq a] [DecidableEq r]

theorem reduced_inverse_identity (P : Matrix a r ℝ) (A : Matrix a a ℝ)
    (H : Matrix r r ℝ) (c : ℝ) (hA : A.PosDef)
    (hT : (c • (Pᵀ * A⁻¹ * P)).PosDef)
    (hM : (A - c • (P * H * Pᵀ)).PosDef) :
    c • (Pᵀ * (A - c • (P * H * Pᵀ))⁻¹ * P) =
      ((c • (Pᵀ * A⁻¹ * P))⁻¹ - H)⁻¹ := by
  let T := c • (Pᵀ * A⁻¹ * P)
  let K := T⁻¹ - H
  let M := A - c • (P * H * Pᵀ)
  let _ := hA.isUnit.invertible
  let _ := hT.isUnit.invertible
  let _ := hM.isUnit.invertible
  have hbase : M * (A⁻¹ * P) = P - P * (H * T) := by
    dsimp [M, T]
    simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_assoc, Matrix.mul_inv_cancel_left_of_invertible]
  have heq : M * (A⁻¹ * P) = P * (K * T) := by
    rw [hbase]
    dsimp [K]
    simp only [Matrix.sub_mul, Matrix.mul_sub,
      Matrix.inv_mul_of_invertible, Matrix.mul_one]
  have heq₂ : A⁻¹ * P = M⁻¹ * P * K * T := by
    have h := congrArg (fun X : Matrix a r ℝ => M⁻¹ * X) heq
    simpa only [Matrix.mul_assoc, Matrix.inv_mul_cancel_left_of_invertible] using h
  have heq₃ : A⁻¹ * P * T⁻¹ = M⁻¹ * P * K := by
    rw [heq₂]
    simp only [Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.mul_one]
  have hleft : (c • (Pᵀ * M⁻¹ * P)) * K = 1 := by
    calc
      (c • (Pᵀ * M⁻¹ * P)) * K = c • (Pᵀ * (M⁻¹ * P * K)) := by
        simp only [Matrix.smul_mul, Matrix.mul_assoc]
      _ = c • (Pᵀ * (A⁻¹ * P * T⁻¹)) := by rw [heq₃]
      _ = T * T⁻¹ := by
        dsimp [T]
        simp only [Matrix.smul_mul, Matrix.mul_assoc]
      _ = 1 := Matrix.mul_inv_of_invertible T
  exact (Matrix.inv_eq_left_inv hleft).symm

end

end HierarchicalLaminates.Lamination
