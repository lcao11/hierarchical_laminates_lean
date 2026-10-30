module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic.NoncommRing

/-!
# Positive matrix order in the lamination formula

Quadratic-form order is expressed by positive-semidefinite matrix
differences.
-/

@[expose] public section

namespace HierarchicalLaminates.Lamination

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A sum-of-squares identity for the difference of two positive inverses. -/
theorem inverse_difference_identity {A B : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.PosDef) :
    A⁻¹ - B⁻¹ =
      (A⁻¹ - B⁻¹)ᴴ * A * (A⁻¹ - B⁻¹) + B⁻¹ᴴ * (B - A) * B⁻¹ := by
  let _ := hA.isUnit.invertible
  let _ := hB.isUnit.invertible
  rw [conjTranspose_sub, hA.inv.isHermitian.eq, hB.inv.isHermitian.eq]
  simp only [sub_mul, mul_sub, Matrix.mul_assoc,
    Matrix.inv_mul_cancel_left_of_invertible, Matrix.mul_inv_of_invertible,
    Matrix.mul_one]
  noncomm_ring

/-- Inversion reverses the positive-semidefinite order on positive matrices. -/
theorem inverse_order_reversal {A B : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hAB : (B - A).PosSemidef) :
    (A⁻¹ - B⁻¹).PosSemidef := by
  rw [inverse_difference_identity hA hB]
  exact (hA.posSemidef.conjTranspose_mul_mul_same (A⁻¹ - B⁻¹)).add
    (hAB.conjTranspose_mul_mul_same B⁻¹)

end HierarchicalLaminates.Lamination
