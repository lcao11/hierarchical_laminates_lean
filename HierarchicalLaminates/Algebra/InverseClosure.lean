module

public import HierarchicalLaminates.Algebra.ParameterSpace

/-!
# Inverse closure of the spin parameter space

The spin-conjugate product expresses the inverse through a scalar denominator.
A left inverse forces this denominator to be nonzero, so inversion preserves
the parameter space for every invertible member, including indefinite matrices.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates

/-- A spin matrix and its conjugate sum to twice its scalar part. -/
theorem spinMatrix_add_conjugate (a : Fin 5 → ℝ) :
    spinMatrix a + spinConjugate a = (2 * a 0) • (1 : RMatrix8) := by
  ext i j
  simp [spinMatrix, spinConjugate]
  ring

/-- A left inverse forces the spin denominator to be nonzero. -/
theorem spinDenom_ne_zero_of_left_inverse_general (a : Fin 5 → ℝ) (B : RMatrix8)
    (hleft : B * spinMatrix a = 1) : spinDenom a ≠ 0 := by
  intro hzero
  have hconj : spinConjugate a = 0 := by
    calc
      spinConjugate a = (1 : RMatrix8) * spinConjugate a := by simp
      _ = (B * spinMatrix a) * spinConjugate a := by rw [hleft]
      _ = B * (spinMatrix a * spinConjugate a) := by rw [mul_assoc]
      _ = 0 := by rw [spinMatrix_mul_conjugate, hzero]; simp
  have ha : a 0 = 0 := by
    have h := congrArg (fun M : RMatrix8 => M 0 0) hconj
    simpa [spinConjugate_diag] using h
  have hmatrix : spinMatrix a = 0 := by
    simpa [hconj, ha] using spinMatrix_add_conjugate a
  have hbad : (0 : RMatrix8) = 1 := by simpa [hmatrix] using hleft
  exact zero_ne_one (congrArg (fun M : RMatrix8 => M 0 0) hbad)

/-- The left inverse of a spin-space member is again a spin-space member. -/
theorem spinMember_of_left_inverse_general {H B : RMatrix8} (hH : SpinMember H)
    (hleft : B * H = 1) : SpinMember B := by
  rcases hH with ⟨a, rfl⟩
  have hright := spinMatrix_mul_inverse a
    (spinDenom_ne_zero_of_left_inverse_general a B hleft)
  have hB : B = spinInverse a := by
    calc
      B = B * (1 : RMatrix8) := by simp
      _ = B * (spinMatrix a * spinInverse a) := by rw [hright]
      _ = (B * spinMatrix a) * spinInverse a := by rw [mul_assoc]
      _ = spinInverse a := by rw [hleft]; simp
  rw [hB]
  exact spinInverse_member a

/-- The parameter space is closed under inversion for matrices with invertible
determinant. Over `ℝ`, this is exactly the nonzero-determinant condition. -/
theorem parameterSpace_inv_mem_of_isUnit {H : RMatrix8} (hH : H ∈ parameterSpace)
    (hinvertible : IsUnit H.det) : H⁻¹ ∈ parameterSpace :=
  spinMember_of_left_inverse_general hH (Matrix.nonsing_inv_mul H hinvertible)

end HierarchicalLaminates
