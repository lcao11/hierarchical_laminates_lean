module

public import HierarchicalLaminates.Algebra.MaterialData
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.BigOperators
public import Mathlib.Tactic.NormNum

/-!
# Real versions of the rational material data

The finite rational identities transfer to real matrices.
-/

@[expose] public section

namespace HierarchicalLaminates

open scoped Matrix

noncomputable section

def realMatrix {m n : ℕ} (A : QMatrix m n) : Matrix (Fin m) (Fin n) ℝ :=
  A.map (algebraMap ℚ ℝ)

def realVector {n : ℕ} (v : Fin n → ℚ) : Fin n → ℝ :=
  fun i => (v i : ℝ)

theorem realMatrix_add {m n : ℕ} (A B : QMatrix m n) :
    realMatrix (A + B) = realMatrix A + realMatrix B := by
  ext i j
  simp [realMatrix]

theorem realMatrix_sub {m n : ℕ} (A B : QMatrix m n) :
    realMatrix (A - B) = realMatrix A - realMatrix B := by
  ext i j
  simp [realMatrix]

theorem realMatrix_mul {l m n : ℕ} (A : QMatrix l m) (B : QMatrix m n) :
    realMatrix (A * B) = realMatrix A * realMatrix B := by
  ext i j
  simp [realMatrix, Matrix.mul_apply, map_sum, map_mul]

theorem realMatrix_transpose {m n : ℕ} (A : QMatrix m n) :
    realMatrix Aᵀ = (realMatrix A)ᵀ := by
  rfl

theorem realMatrix_smul {m n : ℕ} (a : ℚ) (A : QMatrix m n) :
    realMatrix (a • A) = (a : ℝ) • realMatrix A := by
  ext i j
  simp [realMatrix]

theorem realMatrix_zero {m n : ℕ} :
    realMatrix (0 : QMatrix m n) = 0 := by
  ext i j
  simp [realMatrix]

theorem realMatrix_one {n : ℕ} :
    realMatrix (1 : QMatrix n n) = 1 := by
  ext i j
  by_cases hij : i = j
  · simp [realMatrix, Matrix.one_apply, hij]
  · simp [realMatrix, hij]

theorem realMatrix_mulVec {m n : ℕ} (A : QMatrix m n) (v : Fin n → ℚ) :
    realVector (A *ᵥ v) = realMatrix A *ᵥ realVector v := by
  ext i
  simp [realVector, realMatrix, Matrix.mulVec, dotProduct]

def gammaR (j : Fin 4) : Matrix (Fin 8) (Fin 8) ℝ := realMatrix (gammaQ j)

def omegaR : Matrix (Fin 8) (Fin 8) ℝ := realMatrix omegaQ

def factorR : Matrix (Fin 16) (Fin 8) ℝ := realMatrix factorQ

def factorBlockR (j : Fin 4) : Matrix (Fin 4) (Fin 8) ℝ := realMatrix (factorBlockQ j)

def verticalR : Matrix (Fin 16) (Fin 16) ℝ := realMatrix verticalQ

def gammaSumR : Matrix (Fin 8) (Fin 8) ℝ := realMatrix gammaSumQ

def gramR : Matrix (Fin 8) (Fin 8) ℝ := realMatrix gramQ

def gramInvR : Matrix (Fin 8) (Fin 8) ℝ := realMatrix gramInvQ

def unitPlusR : Fin 8 → ℝ := realVector unitPlusQ

def unitMinusR : Fin 8 → ℝ := realVector unitMinusQ

def loadPlusR : Fin 16 → ℝ := realVector loadPlusQ

def loadMinusR : Fin 16 → ℝ := realVector loadMinusQ

def xiR : Matrix (Fin 2) (Fin 16) ℝ := realMatrix xiQ

def etaR : Matrix (Fin 2) (Fin 16) ℝ := realMatrix etaQ

def reducedDifferenceR (M : Matrix (Fin 8) (Fin 8) ℝ) : ℝ :=
  M 0 0 - M 4 4

theorem gammaSumR_eq : gammaSumR = ∑ j : Fin 4, gammaR j := by
  ext i k
  simp [gammaSumR, gammaSumQ, gammaR, realMatrix, Matrix.sum_apply]

theorem gramR_eq : gramR = 1 + (1 / 4 : ℝ) • gammaSumR := by
  change realMatrix (1 + (1 / 4 : ℚ) • gammaSumQ) = _
  rw [realMatrix_add, realMatrix_smul, realMatrix_one]
  norm_num [gammaSumR]

theorem gramInvR_eq :
    gramInvR = (8 / 3 : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ) - (4 / 3 : ℝ) • gramR := by
  change realMatrix ((8 / 3 : ℚ) • (1 : QMatrix 8 8) - (4 / 3 : ℚ) • gramQ) = _
  rw [realMatrix_sub, realMatrix_smul, realMatrix_smul, realMatrix_one]
  norm_num [gramR]

theorem gammaR_transpose (j : Fin 4) : (gammaR j)ᵀ = gammaR j := by
  have h := congrArg realMatrix (gammaQ_transpose j)
  simpa [realMatrix_transpose, gammaR] using h

theorem gammaR_clifford (i j : Fin 4) :
    gammaR i * gammaR j + gammaR j * gammaR i =
      if i = j then (2 : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ) else 0 := by
  have h := congrArg realMatrix (gammaQ_clifford i j)
  by_cases hij : i = j
  · simpa [realMatrix_add, realMatrix_mul, realMatrix_smul, realMatrix_one,
      gammaR, hij] using h
  · simpa [realMatrix_add, realMatrix_mul, realMatrix_zero, gammaR, hij] using h

theorem gammaR_square (j : Fin 4) : gammaR j * gammaR j = 1 := by
  have h := congrArg realMatrix (gammaQ_square j)
  simpa [realMatrix_mul, realMatrix_one, gammaR] using h

theorem gammaR_orientation : gammaR 0 * gammaR 1 * gammaR 2 * gammaR 3 = omegaR := by
  have h := congrArg realMatrix gammaQ_orientation
  simpa [realMatrix_mul, gammaR, omegaR] using h

theorem factorR_gram : factorRᵀ * factorR = gramR := by
  have h := congrArg realMatrix factorQ_gram
  simpa [realMatrix_mul, realMatrix_transpose, factorR, gramR] using h

theorem factorBlockR_gram (j : Fin 4) :
    (factorBlockR j)ᵀ * factorBlockR j =
      (1 / 4 : ℝ) • ((1 : Matrix (Fin 8) (Fin 8) ℝ) + gammaR j) := by
  have h := congrArg realMatrix (factorBlockQ_gram j)
  simpa [realMatrix_mul, realMatrix_transpose, realMatrix_smul, realMatrix_add,
    realMatrix_one, factorBlockR, gammaR] using h

theorem gramR_mul_inv : gramR * gramInvR = 1 := by
  have h := congrArg realMatrix gramQ_mul_inv
  simpa [realMatrix_mul, realMatrix_one, gramR, gramInvR] using h

theorem gramInvR_mul : gramInvR * gramR = 1 := by
  have h := congrArg realMatrix gramInvQ_mul
  simpa [realMatrix_mul, realMatrix_one, gramR, gramInvR] using h

theorem gramR_lower_square :
    gramR - (1 / 2 : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ) =
      (1 / 16 : ℝ) •
        ((gammaSumR + (2 : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ))ᵀ *
          (gammaSumR + (2 : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ))) := by
  have h := congrArg realMatrix gramQ_lower_square
  simpa [realMatrix_sub, realMatrix_smul, realMatrix_one, realMatrix_add,
    realMatrix_mul, realMatrix_transpose, gramR, gammaSumR] using h

theorem gramR_upper_square :
    (3 / 2 : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ) - gramR =
      (1 / 16 : ℝ) •
        ((gammaSumR - (2 : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ))ᵀ *
          (gammaSumR - (2 : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ))) := by
  have h := congrArg realMatrix gramQ_upper_square
  simpa [realMatrix_sub, realMatrix_smul, realMatrix_one,
    realMatrix_mul, realMatrix_transpose, gramR, gammaSumR] using h

theorem factorR_loadPlus : factorRᵀ *ᵥ loadPlusR = unitPlusR := by
  have h := congrArg realVector factorQ_loadPlus
  simpa [realMatrix_mulVec, realMatrix_transpose, factorR, loadPlusR, unitPlusR]
    using h

theorem factorR_loadMinus : factorRᵀ *ᵥ loadMinusR = unitMinusR := by
  have h := congrArg realVector factorQ_loadMinus
  simpa [realMatrix_mulVec, realMatrix_transpose, factorR, loadMinusR, unitMinusR]
    using h

theorem loadPlusR_sq : (∑ i : Fin 16, loadPlusR i * loadPlusR i) = 4 / 3 := by
  have h := congrArg (algebraMap ℚ ℝ) loadPlusQ_sq
  simpa [loadPlusR, realVector, map_sum, map_mul] using h

theorem loadMinusR_sq : (∑ i : Fin 16, loadMinusR i * loadMinusR i) = 4 / 3 := by
  have h := congrArg (algebraMap ℚ ℝ) loadMinusQ_sq
  simpa [loadMinusR, realVector, map_sum, map_mul] using h

theorem xiR_horizontal_row (j : Fin 16) : xiR 0 j = loadPlusR j := by
  simp [xiR, realMatrix, xiQ, loadPlusR, realVector]

theorem etaR_horizontal_row (j : Fin 16) : etaR 0 j = loadMinusR j := by
  simp [etaR, realMatrix, etaQ, loadMinusR, realVector]

theorem xiR_vertical_row (j : Fin 16) : xiR 1 j = 0 := by
  simp [xiR, realMatrix, xiQ]

theorem etaR_vertical_row (j : Fin 16) : etaR 1 j = 0 := by
  simp [etaR, realMatrix, etaQ]

theorem xiR_sq : (∑ i : Fin 2, ∑ j : Fin 16, xiR i j * xiR i j) = 4 / 3 := by
  have h := congrArg (algebraMap ℚ ℝ) xiQ_sq
  simpa [xiR, realMatrix, map_sum, map_mul] using h

theorem etaR_sq : (∑ i : Fin 2, ∑ j : Fin 16, etaR i j * etaR i j) = 4 / 3 := by
  have h := congrArg (algebraMap ℚ ℝ) etaQ_sq
  simpa [etaR, realMatrix, map_sum, map_mul] using h

end

end HierarchicalLaminates
