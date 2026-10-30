module

public import HierarchicalLaminates.Lamination.LayerEnergy
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Equivalent finite-dimensional tensor closures

A real square matrix can be viewed as its array of entries, as an operator on
Euclidean space, or as the Euclidean vector of all its entries. The last norm
is the Frobenius norm. Continuous linear equivalences identify these three
representations, so taking a set's closure commutes with each change of
representation. The conclusions apply to any set of matrices.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.Lamination

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Identify a matrix with its continuous linear action on Euclidean vectors. -/
def matrixOperatorEquiv : Matrix ι ι ℝ ≃L[ℝ]
    (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv

/-- Matrix-to-operator conversion commutes with closure. -/
theorem matrixOperator_image_closure (S : Set (Matrix ι ι ℝ)) :
    matrixOperatorEquiv '' closure S = closure (matrixOperatorEquiv '' S) :=
  matrixOperatorEquiv.toHomeomorph.image_closure S

/-- Coordinate closure membership is equivalent to operator-norm closure membership. -/
theorem matrix_mem_closure_iff_operator (S : Set (Matrix ι ι ℝ)) (A : Matrix ι ι ℝ) :
    A ∈ closure S ↔ matrixOperatorEquiv A ∈ closure (matrixOperatorEquiv '' S) := by
  rw [← matrixOperator_image_closure]
  exact (matrixOperatorEquiv.injective.mem_set_image).symm

/-- Index the entries of a matrix by pairs, without changing their values. -/
def flattenMatrixEquiv : Matrix ι ι ℝ ≃ₗ[ℝ] (ι × ι → ℝ) where
  toFun A p := A p.1 p.2
  invFun v i j := v (i, j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Identify a matrix with its Euclidean vector of entries, whose norm is the
Frobenius norm. -/
def matrixFrobeniusEquiv : Matrix ι ι ℝ ≃L[ℝ] EuclideanSpace ℝ (ι × ι) :=
  (flattenMatrixEquiv.trans (WithLp.linearEquiv 2 ℝ (ι × ι → ℝ)).symm).toContinuousLinearEquiv

/-- The squared Frobenius norm is the sum of the squares of all entries. -/
theorem matrixFrobenius_norm_sq (A : Matrix ι ι ℝ) :
    ‖matrixFrobeniusEquiv A‖ ^ 2 = ∑ p : ι × ι, (A p.1 p.2) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

/-- Conversion to the Frobenius representation commutes with closure. -/
theorem matrixFrobenius_image_closure (S : Set (Matrix ι ι ℝ)) :
    matrixFrobeniusEquiv '' closure S = closure (matrixFrobeniusEquiv '' S) :=
  matrixFrobeniusEquiv.toHomeomorph.image_closure S

/-- Coordinate closure membership is equivalent to Frobenius-norm closure membership. -/
theorem matrix_mem_closure_iff_frobenius (S : Set (Matrix ι ι ℝ)) (A : Matrix ι ι ℝ) :
    A ∈ closure S ↔ matrixFrobeniusEquiv A ∈ closure (matrixFrobeniusEquiv '' S) := by
  rw [← matrixFrobenius_image_closure]
  exact (matrixFrobeniusEquiv.injective.mem_set_image).symm

end HierarchicalLaminates.Lamination
