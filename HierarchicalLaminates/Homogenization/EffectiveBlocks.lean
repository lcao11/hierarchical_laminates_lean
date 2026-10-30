module

public import HierarchicalLaminates.Material.CoefficientLaw

/-!
# The common vertical block of every periodic effective tensor

A constant vertical loading produces a constant flux for both constituents.
Orthogonality of constant fluxes to zero-mean weak gradients and coercivity
identify this field with the cell solution. Symmetry supplies the matching
rows of the effective tensor.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Homogenization

open Matrix MeasureTheory HierarchicalLaminates HierarchicalLaminates.Periodic
  HierarchicalLaminates.Analysis HierarchicalLaminates.Lamination HierarchicalLaminates.Material

/-- A physical loading supported in the vertical spatial direction. -/
def IsVerticalLoading (F : PhysicalGradient) : Prop := ∀ a, F (0, a) = 0

theorem materialTensor_vertical_action (H : RMatrix8) (F : PhysicalGradient)
    (hF : IsVerticalLoading F) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (materialTensor H) F =
      Matrix.toEuclideanCLM (𝕜 := ℝ) phaseZero F := by
  change ∀ a, F.ofLp (0, a) = 0 at hF
  ext ⟨i, a⟩
  change (materialTensor H *ᵥ (F : Fin 2 × Fin 16 → ℝ)) (i, a) =
    (phaseZero *ᵥ (F : Fin 2 × Fin 16 → ℝ)) (i, a)
  fin_cases i <;>
    simp [phaseZero, materialTensor, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, hF]

theorem coefficientOperator_vertical_action (b : PhaseFraction) (q : Domain)
    (F : PhysicalGradient) (hF : IsVerticalLoading F) :
    coefficientOperator b q F = zeroPhaseOperator F := by
  have hone : onePhaseOperator F = zeroPhaseOperator F :=
    materialTensor_vertical_action (rho • (1 : RMatrix8)) F hF
  simp only [coefficientOperator, _root_.add_apply,
    _root_.smul_apply, _root_.sub_apply, hone,
    sub_self, smul_zero, add_zero]

theorem coefficientLaw_constant_vertical (b : PhaseFraction) (F : PhysicalGradient)
    (hF : IsVerticalLoading F) :
    coefficientLaw b (constantField F) = constantField (zeroPhaseOperator F) := by
  apply Lp.ext
  filter_upwards [coefficientLaw_coe b (constantField F),
    Lp.coeFn_const 2 domainMeasure F,
    Lp.coeFn_const 2 domainMeasure (zeroPhaseOperator F)] with q hcoeff hconst hflux
  change constantField F q = F at hconst
  change constantField (zeroPhaseOperator F) q = zeroPhaseOperator F at hflux
  rw [hcoeff, hconst, hflux]
  exact coefficientOperator_vertical_action b q F hF

theorem constant_vertical_isCellField (b : PhaseFraction) (F : PhysicalGradient)
    (hF : IsVerticalLoading F) :
    IsCellField gradientSpace (coefficientLaw b) (constantField F) (constantField F) := by
  constructor
  · simpa only [sub_self] using gradientSpace.zero_mem
  · intro g hg
    rw [coefficientLaw_constant_vertical b F hF, constant_mean_pairing,
      gradientSpace_mean_zero g hg, inner_zero_right]

theorem vertical_cellField_eq_constant (b : PhaseFraction) (F : PhysicalGradient)
    (hF : IsVerticalLoading F) :
    cellField gradientSpace (coefficientLaw b) (1 / 4) (by norm_num)
      (coefficientLaw_coercive b) (constantField F) = constantField F := by
  exact cellField_unique (by norm_num : (0 : ℝ) < 1 / 4)
    (coefficientLaw_coercive b) (cellField_isCellField _ _ _ _ _ _)
    (constant_vertical_isCellField b F hF)

theorem effectiveOperator_vertical_action (b : PhaseFraction) (F : PhysicalGradient)
    (hF : IsVerticalLoading F) :
    HierarchicalLaminates.Material.effectiveOperator b F = zeroPhaseOperator F := by
  change meanField (coefficientLaw b
    (cellField gradientSpace (coefficientLaw b) (1 / 4) (by norm_num)
      (coefficientLaw_coercive b) (constantField F))) = _
  rw [vertical_cellField_eq_constant b F hF,
    coefficientLaw_constant_vertical b F hF, mean_constantField]

theorem effectiveMatrix_isHermitian (b : PhaseFraction) :
    (effectiveMatrix b).IsHermitian := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mp
  change (Matrix.toEuclideanCLM (𝕜 := ℝ) (effectiveMatrix b) :
    PhysicalGradient →ₗ[ℝ] PhysicalGradient).IsSymmetric
  rw [effectiveMatrix_operator]
  exact periodicEffective_symmetric _ (coefficientLaw_symmetric b) _ _ _

theorem effectiveMatrix_vertical_column (b : PhaseFraction)
    (j : Fin 2 × Fin 16) (a : Fin 16) :
    effectiveMatrix b j (1, a) = phaseZero j (1, a) := by
  let F : PhysicalGradient := WithLp.toLp 2 (Pi.single (1, a) (1 : ℝ))
  have hF : IsVerticalLoading F := by
    intro c
    simp [F]
  have h := congrArg (fun v : PhysicalGradient => v j)
    (effectiveOperator_vertical_action b F hF)
  rw [← effectiveMatrix_operator b] at h
  change (effectiveMatrix b *ᵥ Pi.single (1, a) (1 : ℝ)) j =
    (phaseZero *ᵥ Pi.single (1, a) (1 : ℝ)) j at h
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h

theorem effectiveMatrix_vertical_row (b : PhaseFraction)
    (a : Fin 16) (j : Fin 2 × Fin 16) :
    effectiveMatrix b (1, a) j = phaseZero (1, a) j := by
  have hB := (effectiveMatrix_isHermitian b).apply j (1, a)
  have hzero := (materialTensor_isHermitian (Matrix.isHermitian_zero :
    (0 : RMatrix8).IsHermitian)).apply j (1, a)
  simp only [star_trivial] at hB hzero
  change phaseZero (1, a) j = phaseZero j (1, a) at hzero
  exact hB.trans ((effectiveMatrix_vertical_column b j a).trans hzero.symm)

theorem effectiveMatrix_commonVerticalRows (b : PhaseFraction)
    (a : Fin 16) (i : Fin 2) (c : Fin 16) :
    effectiveMatrix b (1, a) (i, c) = if i = 1 then verticalR a c else 0 := by
  rw [effectiveMatrix_vertical_row]
  fin_cases i <;> simp [phaseZero, materialTensor]

theorem effectiveMatrix_spatialBlocks (b : PhaseFraction) :
    effectiveMatrix b = spatialBlocks
      (fun a c => effectiveMatrix b (0, a) (0, c)) verticalR := by
  ext ⟨i, a⟩ ⟨j, c⟩
  fin_cases i <;> fin_cases j
  · simp [spatialBlocks]
  · change effectiveMatrix b (0, a) (1, c) = _
    rw [effectiveMatrix_vertical_column]
    simp [phaseZero, materialTensor, spatialBlocks]
  · change effectiveMatrix b (1, a) (0, c) = _
    rw [effectiveMatrix_vertical_row]
    simp [phaseZero, materialTensor, spatialBlocks]
  · change effectiveMatrix b (1, a) (1, c) = _
    rw [effectiveMatrix_vertical_row]
    simp [phaseZero, materialTensor, spatialBlocks]

theorem effectiveMatrix_posDef (b : PhaseFraction) : (effectiveMatrix b).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (effectiveMatrix_isHermitian b)
  intro v hv
  let F : PhysicalGradient := WithLp.toLp 2 v
  have hF : F ≠ 0 := by
    intro h
    apply hv
    exact congrArg (fun f : PhysicalGradient => (f : Fin 2 × Fin 16 → ℝ)) h
  have hco := periodicEffective_coercive (coefficientLaw b) (1 / 4)
    (by norm_num) (coefficientLaw_coercive b) F
  have hpos : 0 < inner ℝ (HierarchicalLaminates.Material.effectiveOperator b F) F := by
    exact lt_of_lt_of_le (mul_pos (mul_pos (by norm_num) (norm_pos_iff.mpr hF))
      (norm_pos_iff.mpr hF)) hco
  rw [← effectiveMatrix_operator b, real_inner_comm] at hpos
  simpa only [Matrix.inner_toEuclideanCLM, star_trivial] using hpos

end HierarchicalLaminates.Homogenization
