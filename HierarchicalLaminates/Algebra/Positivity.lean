module

public import HierarchicalLaminates.Algebra.Loadings
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Positivity of the material data

Positive-semidefinite matrix differences give the quadratic bounds used for
the horizontal constitutive block.
-/

@[expose] public section

namespace HierarchicalLaminates

open scoped Matrix

noncomputable section

theorem gammaR_add_identity_posSemidef (j : Fin 4) :
    ((1 : Matrix (Fin 8) (Fin 8) ℝ) + gammaR j).PosSemidef := by
  have h : ((1 / 4 : ℝ) • ((1 : Matrix (Fin 8) (Fin 8) ℝ) + gammaR j)).PosSemidef := by
    rw [← factorBlockR_gram]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self (factorBlockR j)
  have hscale := h.smul (show (0 : ℝ) ≤ 4 by norm_num)
  have heq : (4 : ℝ) • ((1 / 4 : ℝ) •
      ((1 : Matrix (Fin 8) (Fin 8) ℝ) + gammaR j)) =
      (1 : Matrix (Fin 8) (Fin 8) ℝ) + gammaR j := by
    rw [smul_smul]
    norm_num
  rw [heq] at hscale
  exact hscale

theorem gramR_lower_posSemidef :
    (gramR - (1 / 2 : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ)).PosSemidef := by
  rw [gramR_lower_square]
  let A : Matrix (Fin 8) (Fin 8) ℝ :=
    gammaSumR + (2 : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ)
  have hstar : A.conjTranspose = A.transpose := by
    ext i j
    simp
  have h := Matrix.posSemidef_conjTranspose_mul_self A
  rw [hstar] at h
  simpa [A] using h.smul (show (0 : ℝ) ≤ 1 / 16 by norm_num)

theorem gramR_upper_posSemidef :
    ((3 / 2 : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ) - gramR).PosSemidef := by
  rw [gramR_upper_square]
  let A : Matrix (Fin 8) (Fin 8) ℝ :=
    gammaSumR - (2 : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ)
  have hstar : A.conjTranspose = A.transpose := by
    ext i j
    simp
  have h := Matrix.posSemidef_conjTranspose_mul_self A
  rw [hstar] at h
  simpa [A] using h.smul (show (0 : ℝ) ≤ 1 / 16 by norm_num)

theorem gramR_posDef : gramR.PosDef := by
  have hId : ((1 / 2 : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ)).PosDef :=
    Matrix.PosDef.one.smul (by norm_num)
  have h := hId.add_posSemidef gramR_lower_posSemidef
  have heq : (1 / 2 : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ) +
      (gramR - (1 / 2 : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ)) = gramR := by
    abel
  rw [heq] at h
  exact h

theorem real_dot_self_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

theorem gramR_quadratic_upper (w : Fin 8 → ℝ) :
    w ⬝ᵥ (gramR *ᵥ w) ≤ (3 / 2 : ℝ) * (w ⬝ᵥ w) := by
  have h := gramR_upper_posSemidef.dotProduct_mulVec_nonneg w
  have h' : 0 ≤ (3 / 2 : ℝ) * (w ⬝ᵥ w) - w ⬝ᵥ (gramR *ᵥ w) := by
    simpa only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul] using h
  linarith

theorem factorR_quadratic_upper (w : Fin 8 → ℝ) :
    (factorR *ᵥ w) ⬝ᵥ (factorR *ᵥ w) ≤ (3 / 2 : ℝ) * (w ⬝ᵥ w) := by
  have heq : (factorR *ᵥ w) ⬝ᵥ (factorR *ᵥ w) = w ⬝ᵥ (gramR *ᵥ w) := by
    rw [← factorR_gram, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec]
  rw [heq]
  exact gramR_quadratic_upper w

/-- The transpose satisfies the same quadratic bound. -/
theorem factorR_transpose_quadratic_upper (v : Fin 16 → ℝ) :
    (factorRᵀ *ᵥ v) ⬝ᵥ (factorRᵀ *ᵥ v) ≤ (3 / 2 : ℝ) * (v ⬝ᵥ v) := by
  let w : Fin 8 → ℝ := factorRᵀ *ᵥ v
  let u : Fin 16 → ℝ := factorR *ᵥ w
  have hrel : v ⬝ᵥ u = w ⬝ᵥ w := by
    dsimp [u, w]
    rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  have hCS : (v ⬝ᵥ u) * (v ⬝ᵥ u) ≤ (v ⬝ᵥ v) * (u ⬝ᵥ u) := by
    simpa only [dotProduct, pow_two] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v u
  rw [hrel] at hCS
  have hu : u ⬝ᵥ u ≤ (3 / 2 : ℝ) * (w ⬝ᵥ w) := factorR_quadratic_upper w
  have hm := mul_le_mul_of_nonneg_left hu (real_dot_self_nonneg v)
  change w ⬝ᵥ w ≤ (3 / 2 : ℝ) * (v ⬝ᵥ v)
  by_cases hw : w ⬝ᵥ w = 0
  · rw [hw]
    exact mul_nonneg (by norm_num) (real_dot_self_nonneg v)
  · have hwpos : 0 < w ⬝ᵥ w :=
      lt_of_le_of_ne (real_dot_self_nonneg w) (Ne.symm hw)
    have hprod : (w ⬝ᵥ w) * (w ⬝ᵥ w) ≤
        ((3 / 2 : ℝ) * (v ⬝ᵥ v)) * (w ⬝ᵥ w) := by
      nlinarith [hCS, hm]
    exact le_of_mul_le_mul_right hprod hwpos

theorem factorR_upper_posSemidef :
    ((3 / 2 : ℝ) • (1 : Matrix (Fin 16) (Fin 16) ℝ) -
      factorR * factorRᵀ).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · have hI : ((3 / 2 : ℝ) • (1 : Matrix (Fin 16) (Fin 16) ℝ)).PosSemidef :=
      Matrix.PosSemidef.one.smul (by norm_num)
    have hP : (factorR * factorRᵀ).IsHermitian := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.isHermitian_mul_conjTranspose_self factorR
    exact hI.isHermitian.sub hP
  · intro v
    have hbound := factorR_transpose_quadratic_upper v
    have heq : v ⬝ᵥ ((factorR * factorRᵀ) *ᵥ v) =
        (factorRᵀ *ᵥ v) ⬝ᵥ (factorRᵀ *ᵥ v) := by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
    have h : 0 ≤ (3 / 2 : ℝ) * (v ⬝ᵥ v) -
        v ⬝ᵥ ((factorR * factorRᵀ) *ᵥ v) := by
      rw [heq]
      linarith
    simpa only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul] using h

theorem factorR_mul_transpose_posSemidef : (factorR * factorRᵀ).PosSemidef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose factorR

theorem horizontalR_upper_posSemidef {H : RMatrix8} (hH : H.PosSemidef) :
    ((1 : Matrix (Fin 16) (Fin 16) ℝ) - horizontalR H).PosSemidef := by
  have h : (factorR * H * factorRᵀ).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hH.mul_mul_conjTranspose_same factorR
  have heq : (1 : Matrix (Fin 16) (Fin 16) ℝ) - horizontalR H =
      factorR * H * factorRᵀ := by
    unfold horizontalR
    abel
  rw [heq]
  exact h

theorem horizontalR_scalar_posDef {r : ℝ} (hr : 0 ≤ r) (hrlt : r < 2 / 3) :
    (horizontalR (r • (1 : Matrix (Fin 8) (Fin 8) ℝ))).PosDef := by
  have hcoef : 0 < 1 - (3 / 2 : ℝ) * r := by linarith
  have hId : ((1 - (3 / 2 : ℝ) * r) •
      (1 : Matrix (Fin 16) (Fin 16) ℝ)).PosDef := Matrix.PosDef.one.smul hcoef
  have hGram := factorR_upper_posSemidef.smul hr
  have heq : horizontalR (r • (1 : Matrix (Fin 8) (Fin 8) ℝ)) =
      (1 - (3 / 2 : ℝ) * r) • (1 : Matrix (Fin 16) (Fin 16) ℝ) +
        r • ((3 / 2 : ℝ) • (1 : Matrix (Fin 16) (Fin 16) ℝ) -
          factorR * factorRᵀ) := by
    simp only [horizontalR, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      smul_sub, smul_smul]
    ext i j
    simp; ring
  rw [heq]
  exact hId.add_posSemidef hGram

/-- The upper parameter bound suffices for horizontal positive definiteness. -/
theorem horizontalR_posDef {r : ℝ} {H : RMatrix8}
    (hupper : (r • (1 : RMatrix8) - H).PosSemidef)
    (hr : 0 ≤ r) (hrlt : r < 2 / 3) : (horizontalR H).PosDef := by
  have hbonus : (factorR * (r • (1 : RMatrix8) - H) * factorRᵀ).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hupper.mul_mul_conjTranspose_same factorR
  have heq : horizontalR H = horizontalR (r • (1 : RMatrix8)) +
      factorR * (r • (1 : RMatrix8) - H) * factorRᵀ := by
    unfold horizontalR
    rw [Matrix.mul_sub, Matrix.sub_mul]
    abel
  rw [heq]
  exact (horizontalR_scalar_posDef hr hrlt).add_posSemidef hbonus

def verticalDiagonalR : Fin 16 → ℝ :=
  ![1, 1, 1, 1, 1 / 2, 1 / 2, 1 / 2, 1 / 2,
    1 / 3, 1 / 3, 1 / 3, 1 / 3, 1 / 4, 1 / 4, 1 / 4, 1 / 4]

set_option maxHeartbeats 0 in
theorem verticalR_diagonal : verticalR = Matrix.diagonal verticalDiagonalR := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [verticalR, realMatrix, verticalQ, verticalDiagonalR, Matrix.diagonal_apply]

theorem verticalR_posDef : verticalR.PosDef := by
  rw [verticalR_diagonal]
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i <;> norm_num [verticalDiagonalR]

theorem verticalR_lower_posSemidef :
    (verticalR - (1 / 4 : ℝ) • (1 : Matrix (Fin 16) (Fin 16) ℝ)).PosSemidef := by
  rw [verticalR_diagonal]
  have heq : Matrix.diagonal verticalDiagonalR -
      (1 / 4 : ℝ) • (1 : Matrix (Fin 16) (Fin 16) ℝ) =
      Matrix.diagonal (fun i => verticalDiagonalR i - 1 / 4) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [heq]
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num [verticalDiagonalR]

theorem verticalR_upper_posSemidef :
    ((1 : Matrix (Fin 16) (Fin 16) ℝ) - verticalR).PosSemidef := by
  rw [verticalR_diagonal]
  have heq : (1 : Matrix (Fin 16) (Fin 16) ℝ) - Matrix.diagonal verticalDiagonalR =
      Matrix.diagonal (fun i => 1 - verticalDiagonalR i) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [heq]
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num [verticalDiagonalR]

end

end HierarchicalLaminates
