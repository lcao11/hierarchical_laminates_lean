module

public import HierarchicalLaminates.GClosure.Interfaces
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Data.Int.GCD

/-! Integer unimodular coordinate changes on the normalized periodic cell. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open MeasureTheory Matrix HierarchicalLaminates.Periodic

instance domainMeasure_addHaar : domainMeasure.IsAddHaarMeasure := by
  dsimp [domainMeasure]
  infer_instance

abbrev IntegerSpatialMatrix := Matrix (Fin 2) (Fin 2) ℤ

def matrixTorus (A : IntegerSpatialMatrix) (q : Domain) : Domain :=
  fun i => A i 0 • q 0 + A i 1 • q 1

def matrixTorusHom (A : IntegerSpatialMatrix) : Domain →+ Domain where
  toFun := matrixTorus A
  map_zero' := by ext i; simp [matrixTorus]
  map_add' := by intro q p; ext i; simp [matrixTorus]; abel

theorem matrixTorus_continuous (A : IntegerSpatialMatrix) : Continuous (matrixTorus A) := by
  apply continuous_pi
  intro i
  exact ((continuous_zsmul (A i 0)).comp (continuous_apply 0)).add
    ((continuous_zsmul (A i 1)).comp (continuous_apply 1))

theorem matrixTorus_one (q : Domain) : matrixTorus 1 q = q := by
  ext i
  fin_cases i
  · change (1 : ℤ) • q 0 + (0 : ℤ) • q 1 = q 0
    simp
  · change (0 : ℤ) • q 0 + (1 : ℤ) • q 1 = q 1
    simp

theorem matrixTorus_mul (A B : IntegerSpatialMatrix) (q : Domain) :
    matrixTorus (A * B) q = matrixTorus A (matrixTorus B q) := by
  ext i
  simp only [matrixTorus, Matrix.mul_apply, Fin.sum_univ_two,
    add_zsmul, zsmul_add, mul_zsmul]
  abel

structure TorusCoordinates where
  matrix : IntegerSpatialMatrix
  inverse : IntegerSpatialMatrix
  inverse_mul : inverse * matrix = 1
  mul_inverse : matrix * inverse = 1

def TorusCoordinates.equiv (R : TorusCoordinates) : Domain ≃+ Domain where
  toFun := matrixTorus R.matrix
  invFun := matrixTorus R.inverse
  left_inv q := by rw [← matrixTorus_mul, R.inverse_mul, matrixTorus_one]
  right_inv q := by rw [← matrixTorus_mul, R.mul_inverse, matrixTorus_one]
  map_add' := (matrixTorusHom R.matrix).map_add

theorem TorusCoordinates.continuous (R : TorusCoordinates) : Continuous R.equiv :=
  matrixTorus_continuous R.matrix

theorem TorusCoordinates.continuous_symm (R : TorusCoordinates) : Continuous R.equiv.symm :=
  matrixTorus_continuous R.inverse

theorem TorusCoordinates.measurePreserving (R : TorusCoordinates) :
    MeasurePreserving R.equiv domainMeasure domainMeasure := by
  exact R.equiv.toAddMonoidHom.measurePreserving R.continuous R.equiv.surjective rfl

theorem TorusCoordinates.measurePreserving_symm (R : TorusCoordinates) :
    MeasurePreserving R.equiv.symm domainMeasure domainMeasure := by
  exact R.equiv.symm.toAddMonoidHom.measurePreserving R.continuous_symm R.equiv.symm.surjective rfl

theorem TorusCoordinates.integral (R : TorusCoordinates) (f : Domain → ℝ)
    (hf : Measurable f) : (∫ q, f (R.equiv q) ∂domainMeasure) = ∫ q, f q ∂domainMeasure := by
  have hp := R.measurePreserving
  have hfm : AEStronglyMeasurable f (Measure.map R.equiv domainMeasure) := by
    rw [hp.map_eq]
    exact hf.aestronglyMeasurable
  have h := integral_map hp.aemeasurable hfm
  rw [hp.map_eq] at h
  exact h.symm

end HierarchicalLaminates.GClosure
