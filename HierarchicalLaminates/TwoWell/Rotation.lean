module

public import HierarchicalLaminates.TwoWell.Base

/-! Clockwise spatial rotation and complementary quadratic energies. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.TwoWell

open Matrix HierarchicalLaminates HierarchicalLaminates.Lamination

@[simp] theorem rotate_zero_row (F : Gradient16) (a : Fin 16) :
    rotate F (0,a) = F (1,a) := by simp [rotate]

@[simp] theorem rotate_one_row (F : Gradient16) (a : Fin 16) :
    rotate F (1,a) = -F (0,a) := by simp [rotate]

theorem rotate_add (F H : Gradient16) : rotate (F+H) = rotate F+rotate H := by
  ext ⟨i,a⟩
  fin_cases i
  · simp [rotate]
  · simp [rotate]
    ring

theorem rotate_sub (F H : Gradient16) : rotate (F-H) = rotate F-rotate H := by
  ext ⟨i,a⟩
  fin_cases i
  · simp [rotate]
  · simp [rotate]
    ring

theorem rotate_smul (r : ℝ) (F : Gradient16) : rotate (r • F) = r • rotate F := by
  ext ⟨i,a⟩
  fin_cases i <;> simp [rotate]

@[simp] theorem rotate_rotate (F : Gradient16) : rotate (rotate F) = -F := by
  ext ⟨i,a⟩
  fin_cases i <;> simp [rotate]

theorem rotate_injective : Function.Injective rotate := by
  intro F H h
  have hh := congrArg rotate h
  simpa using hh

theorem rotationMatrix_mulVec (F : Gradient16) : rotationMatrix *ᵥ F = rotate F := by
  ext ⟨i,a⟩
  fin_cases i <;>
    simp [rotationMatrix, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, rotate]

theorem rotationMatrix_transpose : rotationMatrixᵀ = -rotationMatrix := by
  ext ⟨i,a⟩ ⟨j,b⟩
  fin_cases i <;> fin_cases j <;> by_cases h : a = b <;>
    simp [rotationMatrix, h, eq_comm]

theorem rotationMatrix_transpose_mulVec (F : Gradient16) :
    rotationMatrixᵀ *ᵥ F = -rotate F := by
  rw [rotationMatrix_transpose, Matrix.neg_mulVec, rotationMatrix_mulVec]

theorem rotationMatrix_orthogonal : rotationMatrixᵀ * rotationMatrix = 1 := by
  ext ⟨i,a⟩ ⟨j,b⟩
  fin_cases i <;> fin_cases j <;> by_cases h : a = b <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, rotationMatrix,
      Matrix.one_apply, h, eq_comm]

theorem rotationMatrix_orthogonal' : rotationMatrix * rotationMatrixᵀ = 1 := by
  rw [rotationMatrix_transpose, Matrix.mul_neg, ← Matrix.neg_mul,
    ← rotationMatrix_transpose, rotationMatrix_orthogonal]

theorem dual_posDef {A : Tensor16} (hA : A.PosDef) : (dual A).PosDef := by
  have hinj : Function.Injective (rotationMatrixᵀ : Tensor16).mulVec := by
    intro F H hh
    rw [rotationMatrix_transpose_mulVec, rotationMatrix_transpose_mulVec] at hh
    exact rotate_injective (neg_injective hh)
  simpa only [dual, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.transpose_transpose] using hA.inv.conjTranspose_mul_mul_same hinj

theorem dual_quadratic (A : Tensor16) (F : Gradient16) :
    quadraticEnergy (dual A) F = quadraticEnergy A⁻¹ (-rotate F) := by
  change quadraticFormValue (rotationMatrix * A⁻¹ * rotationMatrixᵀ) F = _
  have h := quadratic_sandwich A⁻¹ rotationMatrixᵀ F
  simpa only [Matrix.transpose_transpose, rotationMatrix_transpose_mulVec,
    quadraticFormValue, quadraticEnergy] using h

theorem quadraticEnergy_neg (A : Tensor16) (F : Gradient16) :
    quadraticEnergy A (-F) = quadraticEnergy A F := by
  simp [quadraticEnergy, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg]

theorem dual_quadratic_rotate (A : Tensor16) (F : Gradient16) :
    quadraticEnergy (dual A) (rotate F) = quadraticEnergy A⁻¹ F := by
  rw [dual_quadratic, rotate_rotate, neg_neg]

theorem dual_mul_rotate {A : Tensor16} (hA : A.PosDef) (F : Gradient16) :
    dual A *ᵥ rotate (A *ᵥ F) = rotate F := by
  let := hA.isUnit.invertible
  rw [dual, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    rotationMatrix_transpose_mulVec, rotate_rotate, neg_neg,
    Matrix.mulVec_mulVec]
  simp [rotationMatrix_mulVec]

theorem rotate_dot_rotate (F H : Gradient16) : rotate F ⬝ᵥ rotate H = F ⬝ᵥ H := by
  simp [dotProduct, Fintype.sum_prod_type, rotate]
  ring

theorem rotate_continuous : Continuous rotate := by
  apply continuous_pi
  rintro ⟨i,a⟩
  fin_cases i
  · simpa [rotate] using (continuous_apply (1,a) : Continuous (fun F : Gradient16 => F (1,a)))
  · simpa [rotate] using (continuous_apply (0,a) : Continuous (fun F : Gradient16 => F (0,a))).neg

theorem dual_energy_flux {A : Tensor16} (hA : A.PosDef) (F : Gradient16) :
    quadraticEnergy (dual A) (rotate (A *ᵥ F)) = quadraticEnergy A F := by
  change rotate (A *ᵥ F) ⬝ᵥ dual A *ᵥ rotate (A *ᵥ F) = F ⬝ᵥ A *ᵥ F
  rw [dual_mul_rotate hA, rotate_dot_rotate]
  exact dotProduct_comm _ _

theorem pairedEnergy_nonneg {A : Tensor16} (hA : A.PosDef) (F : PairedGradient) :
    0 ≤ pairedEnergy A F := by
  exact add_nonneg (hA.posSemidef.dotProduct_mulVec_nonneg F.1)
    ((dual_posDef hA).posSemidef.dotProduct_mulVec_nonneg F.2)

theorem quadraticEnergy_smul (A : Tensor16) (r : ℝ) (F : Gradient16) :
    quadraticEnergy A (r • F) = r^2*quadraticEnergy A F := by
  simp only [quadraticEnergy, Matrix.mulVec_smul, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  ring

theorem pairedEnergy_homogeneous (A : Tensor16) (r : ℝ) (F : PairedGradient) :
    pairedEnergy A (r • F) = r^2*pairedEnergy A F := by
  change quadraticEnergy A (r • F.1) + quadraticEnergy (dual A) (r • F.2) = _
  rw [quadraticEnergy_smul, quadraticEnergy_smul]
  unfold pairedEnergy
  ring

end HierarchicalLaminates.TwoWell
