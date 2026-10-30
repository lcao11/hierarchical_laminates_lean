module

public import HierarchicalLaminates.Algebra.RealData
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The five-dimensional parameter space

A left-inverse identity and a positive diagonal entry give inverse closure.
Positive-definite matrices and their inverses satisfy these hypotheses.
-/

@[expose] public section

namespace HierarchicalLaminates

open scoped Matrix

noncomputable section

abbrev RMatrix8 := Matrix (Fin 8) (Fin 8) ℝ

def spinMatrix (a : Fin 5 → ℝ) : RMatrix8 :=
  a 0 • (1 : RMatrix8) + a 1 • gammaR 0 + a 2 • gammaR 1 +
    a 3 • gammaR 2 + a 4 • gammaR 3

def spinConjugate (a : Fin 5 → ℝ) : RMatrix8 :=
  a 0 • (1 : RMatrix8) - a 1 • gammaR 0 - a 2 • gammaR 1 -
    a 3 • gammaR 2 - a 4 • gammaR 3

def spinDenom (a : Fin 5 → ℝ) : ℝ :=
  a 0 ^ 2 - a 1 ^ 2 - a 2 ^ 2 - a 3 ^ 2 - a 4 ^ 2

def SpinMember (H : RMatrix8) : Prop := ∃ a : Fin 5 → ℝ, H = spinMatrix a

theorem spinMatrix_diag (a : Fin 5 → ℝ) : spinMatrix a 0 0 = a 0 := by
  simp [spinMatrix, gammaR, realMatrix, gammaQ]

theorem spinConjugate_diag (a : Fin 5 → ℝ) : spinConjugate a 0 0 = a 0 := by
  simp [spinConjugate, gammaR, realMatrix, gammaQ]

theorem spinMatrix_transpose (a : Fin 5 → ℝ) : (spinMatrix a)ᵀ = spinMatrix a := by
  simp [spinMatrix, Matrix.transpose_add, Matrix.transpose_smul, gammaR_transpose]

theorem spinMatrix_add (a b : Fin 5 → ℝ) :
    spinMatrix (a + b) = spinMatrix a + spinMatrix b := by
  ext i j
  simp [spinMatrix, add_smul]; ring

theorem spinMatrix_smul (s : ℝ) (a : Fin 5 → ℝ) :
    spinMatrix (s • a) = s • spinMatrix a := by
  ext i j
  simp [spinMatrix]; ring

theorem spinMember_zero : SpinMember (0 : RMatrix8) := by
  refine ⟨0, ?_⟩
  simp [spinMatrix]

theorem spinMember_one : SpinMember (1 : RMatrix8) := by
  refine ⟨![1, 0, 0, 0, 0], ?_⟩
  simp [spinMatrix]

theorem spinMember_add {H K : RMatrix8} (hH : SpinMember H) (hK : SpinMember K) :
    SpinMember (H + K) := by
  rcases hH with ⟨a, rfl⟩
  rcases hK with ⟨b, rfl⟩
  exact ⟨a + b, (spinMatrix_add a b).symm⟩

theorem spinMember_smul (s : ℝ) {H : RMatrix8} (hH : SpinMember H) :
    SpinMember (s • H) := by
  rcases hH with ⟨a, rfl⟩
  exact ⟨s • a, (spinMatrix_smul s a).symm⟩

theorem spinMember_neg {H : RMatrix8} (hH : SpinMember H) : SpinMember (-H) := by
  simpa using spinMember_smul (-1) hH

theorem spinMember_sub {H K : RMatrix8} (hH : SpinMember H) (hK : SpinMember K) :
    SpinMember (H - K) := by
  simpa [sub_eq_add_neg] using spinMember_add hH (spinMember_neg hK)

def parameterSpace : Submodule ℝ RMatrix8 where
  carrier := {H | SpinMember H}
  zero_mem' := spinMember_zero
  add_mem' := spinMember_add
  smul_mem' := spinMember_smul

theorem mem_parameterSpace_iff (H : RMatrix8) : H ∈ parameterSpace ↔ SpinMember H :=
  Iff.rfl

theorem parameterSpace_one_mem : (1 : RMatrix8) ∈ parameterSpace := spinMember_one

theorem parameterSpace_gamma_mem (j : Fin 4) : gammaR j ∈ parameterSpace := by
  refine ⟨fun i : Fin 5 => if i = j.succ then 1 else 0, ?_⟩
  fin_cases j <;> simp [spinMatrix]

theorem parameterSpace_gram_mem : gramR ∈ parameterSpace := by
  rw [gramR_eq, gammaSumR_eq]
  exact parameterSpace.add_mem parameterSpace_one_mem
    (parameterSpace.smul_mem _ (parameterSpace.sum_mem fun j _ => parameterSpace_gamma_mem j))

theorem parameterSpace_gramInv_mem : gramInvR ∈ parameterSpace := by
  rw [gramInvR_eq]
  exact parameterSpace.sub_mem (parameterSpace.smul_mem _ parameterSpace_one_mem)
    (parameterSpace.smul_mem _ parameterSpace_gram_mem)

set_option maxHeartbeats 0 in
theorem spinMatrix_mul_conjugate (a : Fin 5 → ℝ) :
    spinMatrix a * spinConjugate a = spinDenom a • (1 : RMatrix8) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [spinMatrix, spinConjugate, spinDenom, gammaR, realMatrix, gammaQ,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;> ring

set_option maxHeartbeats 0 in
theorem spinConjugate_mul (a : Fin 5 → ℝ) :
    spinConjugate a * spinMatrix a = spinDenom a • (1 : RMatrix8) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [spinMatrix, spinConjugate, spinDenom, gammaR, realMatrix, gammaQ,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;> ring

theorem spinDenom_ne_zero_of_left_inverse (a : Fin 5 → ℝ) (B : RMatrix8)
    (hleft : B * spinMatrix a = 1) (hdiag : 0 < a 0) : spinDenom a ≠ 0 := by
  intro hzero
  have hconj : spinConjugate a = 0 := by
    calc
      spinConjugate a = (1 : RMatrix8) * spinConjugate a := by simp
      _ = (B * spinMatrix a) * spinConjugate a := by rw [hleft]
      _ = B * (spinMatrix a * spinConjugate a) := by rw [mul_assoc]
      _ = 0 := by rw [spinMatrix_mul_conjugate, hzero]; simp
  have hentry := congrArg (fun M : RMatrix8 => M 0 0) hconj
  have hz : a 0 = 0 := by simpa [spinConjugate_diag] using hentry
  linarith

def spinInverse (a : Fin 5 → ℝ) : RMatrix8 := (spinDenom a)⁻¹ • spinConjugate a

theorem spinMatrix_mul_inverse (a : Fin 5 → ℝ) (hden : spinDenom a ≠ 0) :
    spinMatrix a * spinInverse a = 1 := by
  rw [spinInverse, mul_smul_comm, spinMatrix_mul_conjugate, smul_smul]
  simp [hden]

theorem spinInverse_mul (a : Fin 5 → ℝ) (hden : spinDenom a ≠ 0) :
    spinInverse a * spinMatrix a = 1 := by
  rw [spinInverse, smul_mul_assoc, spinConjugate_mul, smul_smul]
  simp [hden]

def spinInverseCoordinates (a : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![(spinDenom a)⁻¹ * a 0, -(spinDenom a)⁻¹ * a 1,
    -(spinDenom a)⁻¹ * a 2, -(spinDenom a)⁻¹ * a 3,
    -(spinDenom a)⁻¹ * a 4]

theorem spinInverse_eq (a : Fin 5 → ℝ) :
    spinInverse a = spinMatrix (spinInverseCoordinates a) := by
  ext i j
  simp [spinInverse, spinConjugate, spinMatrix, spinInverseCoordinates]; ring

theorem spinInverse_member (a : Fin 5 → ℝ) : SpinMember (spinInverse a) :=
  ⟨spinInverseCoordinates a, spinInverse_eq a⟩

/-- Inverse closure from a left-inverse identity and a positive diagonal entry. -/
theorem spinMember_of_left_inverse {H B : RMatrix8} (hH : SpinMember H)
    (hleft : B * H = 1) (hdiag : 0 < H 0 0) : SpinMember B := by
  rcases hH with ⟨a, rfl⟩
  have ha : 0 < a 0 := by simpa [spinMatrix_diag] using hdiag
  have hden := spinDenom_ne_zero_of_left_inverse a B hleft ha
  have hright := spinMatrix_mul_inverse a hden
  have hB : B = spinInverse a := by
    calc
      B = B * (1 : RMatrix8) := by simp
      _ = B * (spinMatrix a * spinInverse a) := by rw [hright]
      _ = (B * spinMatrix a) * spinInverse a := by rw [mul_assoc]
      _ = spinInverse a := by rw [hleft]; simp
  rw [hB]
  exact spinInverse_member a

theorem spinMember_inv {H : RMatrix8} (hH : SpinMember H) (hpos : H.PosDef) :
    SpinMember H⁻¹ := by
  exact spinMember_of_left_inverse hH
    (Matrix.nonsing_inv_mul H (isUnit_iff_ne_zero.mpr (ne_of_gt hpos.det_pos)))
    hpos.diag_pos

theorem parameterSpace_inv_mem {H : RMatrix8} (hH : H ∈ parameterSpace)
    (hpos : H.PosDef) : H⁻¹ ∈ parameterSpace :=
  spinMember_inv hH hpos

theorem reducedDifferenceR_spin (a : Fin 5 → ℝ) :
    reducedDifferenceR (spinMatrix a) = 0 := by
  simp [reducedDifferenceR, spinMatrix, gammaR, realMatrix, gammaQ]

theorem reducedDifferenceR_zero_of_spinMember {H : RMatrix8} (hH : SpinMember H) :
    reducedDifferenceR H = 0 := by
  rcases hH with ⟨a, rfl⟩
  exact reducedDifferenceR_spin a

end

end HierarchicalLaminates
