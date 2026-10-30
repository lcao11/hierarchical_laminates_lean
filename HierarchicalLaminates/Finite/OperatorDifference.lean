module

public import HierarchicalLaminates.Finite.AnalyticCorrespondence

/-! A continuous loading-difference functional on real reduced operators. -/

@[expose] public section

namespace HierarchicalLaminates

noncomputable section

open Fourier

def reducedUnitPlus : ReducedSpace := EuclideanSpace.basisFun (Fin 8) ℝ 0
def reducedUnitMinus : ReducedSpace := EuclideanSpace.basisFun (Fin 8) ℝ 4

theorem reducedUnitPlus_norm : ‖reducedUnitPlus‖ = 1 :=
  (EuclideanSpace.basisFun (Fin 8) ℝ).norm_eq_one 0

theorem reducedUnitMinus_norm : ‖reducedUnitMinus‖ = 1 :=
  (EuclideanSpace.basisFun (Fin 8) ℝ).norm_eq_one 4

def operatorDifferenceLinear : ReducedOperator →ₗ[ℝ] ℝ where
  toFun A := inner ℝ reducedUnitPlus (A reducedUnitPlus) -
    inner ℝ reducedUnitMinus (A reducedUnitMinus)
  map_add' A B := by simp only [add_apply, inner_add_right]; ring
  map_smul' a A := by simp only [smul_apply, inner_smul_right, RingHom.id_apply]; ring

theorem operatorDifferenceLinear_bound (A : ReducedOperator) :
    |operatorDifferenceLinear A| ≤ 2 * ‖A‖ := by
  have hp : |inner ℝ reducedUnitPlus (A reducedUnitPlus)| ≤ ‖A‖ := by
    calc
      _ ≤ ‖reducedUnitPlus‖ * ‖A reducedUnitPlus‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖reducedUnitPlus‖ * (‖A‖ * ‖reducedUnitPlus‖) :=
        mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)
      _ = ‖A‖ := by rw [reducedUnitPlus_norm]; ring
  have hm : |inner ℝ reducedUnitMinus (A reducedUnitMinus)| ≤ ‖A‖ := by
    calc
      _ ≤ ‖reducedUnitMinus‖ * ‖A reducedUnitMinus‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖reducedUnitMinus‖ * (‖A‖ * ‖reducedUnitMinus‖) :=
        mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)
      _ = ‖A‖ := by rw [reducedUnitMinus_norm]; ring
  change |inner ℝ reducedUnitPlus (A reducedUnitPlus) -
    inner ℝ reducedUnitMinus (A reducedUnitMinus)| ≤ _
  have ht := abs_sub_le (inner ℝ reducedUnitPlus (A reducedUnitPlus)) 0
    (inner ℝ reducedUnitMinus (A reducedUnitMinus))
  simp only [sub_zero, zero_sub, abs_neg] at ht
  exact ht.trans (by linarith)

def operatorDifference : ReducedOperator →L[ℝ] ℝ :=
  operatorDifferenceLinear.mkContinuous 2 (fun A => by
    simpa only [Real.norm_eq_abs] using operatorDifferenceLinear_bound A)

theorem operatorDifference_bound (A : ReducedOperator) :
    |operatorDifference A| ≤ 2 * ‖A‖ := operatorDifferenceLinear_bound A

theorem operatorDifference_matrix (A : Matrix (Fin 8) (Fin 8) ℝ) :
    operatorDifference (Matrix.toEuclideanCLM (n := Fin 8) (𝕜 := ℝ) A) =
      reducedDifferenceR A := by
  change inner ℝ reducedUnitPlus (Matrix.toEuclideanCLM (n := Fin 8) (𝕜 := ℝ) A reducedUnitPlus) -
    inner ℝ reducedUnitMinus (Matrix.toEuclideanCLM (n := Fin 8) (𝕜 := ℝ) A reducedUnitMinus) = _
  rw [Matrix.inner_toEuclideanCLM, Matrix.inner_toEuclideanCLM]
  simp [reducedUnitPlus, reducedUnitMinus, EuclideanSpace.basisFun_apply,
    reducedDifferenceR, dotProduct, Matrix.mulVec, EuclideanSpace.single,
    PiLp.single_apply]

theorem operatorDifference_matrixQ (A : QMatrix 8 8) :
    operatorDifference (matrixOperatorQ A) = (reducedDifferenceQ A : ℝ) := by
  rw [matrixOperatorQ, operatorDifference_matrix, ← reducedDifferenceQ_cast]

end
end HierarchicalLaminates
