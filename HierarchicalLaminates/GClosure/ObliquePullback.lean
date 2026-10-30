module

public import HierarchicalLaminates.GClosure.ObliqueDerivatives

/-!
# Pullback of regular potentials and L² fields by periodic integer coordinates
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open MeasureTheory HierarchicalLaminates.Periodic HierarchicalLaminates.Composition

def spatialGradientLinear (A : IntegerSpatialMatrix) : PhysicalGradient →ₗ[ℝ] PhysicalGradient where
  toFun v := WithLp.toLp 2 (fun p =>
    (A 0 p.1 : ℝ) * v (0,p.2) + (A 1 p.1 : ℝ) * v (1,p.2))
  map_add' := by intro v w; ext p; simp; ring
  map_smul' := by intro c v; ext p; simp; ring

def spatialGradientMap (A : IntegerSpatialMatrix) : PhysicalGradient →L[ℝ] PhysicalGradient :=
  (spatialGradientLinear A).toContinuousLinearMap

theorem spatialGradientMap_apply (A : IntegerSpatialMatrix) (v : PhysicalGradient)
    (i : Fin 2) (c : Fin 16) :
    spatialGradientMap A v (i,c) =
      (A 0 i : ℝ) * v (0,c) + (A 1 i : ℝ) * v (1,c) := rfl

theorem spatialGradientMap_one : spatialGradientMap 1 = ContinuousLinearMap.id ℝ PhysicalGradient := by
  ext v ⟨i,c⟩
  fin_cases i <;>
    change _ + _ = _ <;>
    norm_num [spatialGradientMap_apply, Matrix.one_apply]

theorem spatialGradientMap_comp (A B : IntegerSpatialMatrix) :
    (spatialGradientMap A).comp (spatialGradientMap B) = spatialGradientMap (B * A) := by
  ext v ⟨i,c⟩
  simp only [ContinuousLinearMap.comp_apply, spatialGradientMap_apply,
    Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  ring

theorem matrixTorus_coordinateFlow (A : IntegerSpatialMatrix) (i : Fin 2)
    (q : Domain) (s : ℝ) :
    matrixTorus A (coordinateFlow i q s) =
      linearFlow (matrixTorus A q) (fun j => (A j i : ℝ)) s := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [matrixTorus, coordinateFlow, linearFlow, pairFlow]
  all_goals
    rw [← AddCircle.coe_zsmul]
    simp only [zsmul_eq_mul]
    abel

def transformPotential (A : IntegerSpatialMatrix) (u : RegularPotential) : RegularPotential where
  potential c := (u.potential c).comp ⟨matrixTorus A, matrixTorus_continuous A⟩
  gradient := ⟨fun q => spatialGradientMap A (u.gradient (matrixTorus A q)),
    (spatialGradientMap A).continuous.comp (u.gradient.continuous.comp (matrixTorus_continuous A))⟩
  hasPartial i c q t := by
    have h := RegularPotential.hasDerivAt_linearFlow u c (matrixTorus A q)
      (fun j => (A j i : ℝ)) t
    convert h using 1
    · ext s
      exact congrArg (u.potential c) (matrixTorus_coordinateFlow A i q s)
    · rw [← matrixTorus_coordinateFlow]
      rfl

theorem transformPotential_value (A : IntegerSpatialMatrix) (u : RegularPotential)
    (c : Fin 16) (q : Domain) :
    (transformPotential A u).potential c q = u.potential c (matrixTorus A q) := rfl

theorem transformPotential_gradient (A : IntegerSpatialMatrix) (u : RegularPotential)
    (q : Domain) :
    (transformPotential A u).gradient q = spatialGradientMap A (u.gradient (matrixTorus A q)) := rfl

def TorusCoordinates.pullbackField (R : TorusCoordinates) : PhysicalField →ₗᵢ[ℝ] PhysicalField :=
  Lp.compMeasurePreservingₗᵢ ℝ R.equiv R.measurePreserving

theorem TorusCoordinates.pullbackField_coe (R : TorusCoordinates) (f : PhysicalField) :
    R.pullbackField f =ᵐ[domainMeasure] fun q => f (R.equiv q) :=
  Lp.coeFn_compMeasurePreserving f R.measurePreserving

theorem TorusCoordinates.pullbackField_norm (R : TorusCoordinates) (f : PhysicalField) :
    ‖R.pullbackField f‖ = ‖f‖ := R.pullbackField.norm_map f

end HierarchicalLaminates.GClosure
