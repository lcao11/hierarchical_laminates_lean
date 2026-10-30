module

public import HierarchicalLaminates.Material.ScalarMultiplication
public import HierarchicalLaminates.Material.FieldLaws
public import HierarchicalLaminates.Material.PhaseBounds
public import HierarchicalLaminates.Periodic.CellEnergy
public import Mathlib.Tactic.Module

/-!
# Bounded periodic mixtures of the prescribed phases

The L² operator acts pointwise by the matrix coefficient. Its effective
tensor represents the periodic weak Sobolev cell energy.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Material

open MeasureTheory Matrix
open HierarchicalLaminates.Periodic HierarchicalLaminates.Analysis HierarchicalLaminates.Lamination

structure PhaseFraction where
  value : Domain → ℝ
  measurable : Measurable value
  lower : ∀ q, 0 ≤ value q
  upper : ∀ q, value q ≤ 1

def PhaseFraction.bounded (b : PhaseFraction) : BoundedScalar where
  value := b.value
  measurable := b.measurable
  bound := 1
  bound_nonneg := zero_le_one
  abs_le := fun q => by rw [abs_of_nonneg (b.lower q)]; exact b.upper q

def zeroPhaseOperator : PhysicalGradient →L[ℝ] PhysicalGradient :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) phaseZero

def onePhaseOperator : PhysicalGradient →L[ℝ] PhysicalGradient :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (phaseOne rho)

def coefficientOperator (b : PhaseFraction) (q : Domain) :
    PhysicalGradient →L[ℝ] PhysicalGradient :=
  zeroPhaseOperator + b.value q • (onePhaseOperator - zeroPhaseOperator)

theorem mixtureTensor_affine (t : ℝ) :
    mixtureTensor t = phaseZero + t • (phaseOne rho - phaseZero) := by
  unfold mixtureTensor
  module

theorem coefficientOperator_eq_matrix (b : PhaseFraction) (q : Domain) :
    coefficientOperator b q = Matrix.toEuclideanCLM (𝕜 := ℝ) (mixtureTensor (b.value q)) := by
  rw [mixtureTensor_affine]
  simp only [map_add, map_smul, map_sub]
  rfl

def coefficientLaw (b : PhaseFraction) : PhysicalField →L[ℝ] PhysicalField :=
  zeroPhaseOperator.compLpL 2 domainMeasure +
    (scalarMultiplication b.bounded).comp
      ((onePhaseOperator - zeroPhaseOperator).compLpL 2 domainMeasure)

theorem coefficientLaw_coe (b : PhaseFraction) (f : PhysicalField) :
    coefficientLaw b f =ᵐ[domainMeasure] fun q => coefficientOperator b q (f q) := by
  change ((zeroPhaseOperator.compLpL 2 domainMeasure f) +
    scalarMultiplication b.bounded
      ((onePhaseOperator - zeroPhaseOperator).compLpL 2 domainMeasure f)) =ᵐ[domainMeasure] _
  filter_upwards [Lp.coeFn_add (zeroPhaseOperator.compLpL 2 domainMeasure f)
      (scalarMultiplication b.bounded
        ((onePhaseOperator - zeroPhaseOperator).compLpL 2 domainMeasure f)),
    zeroPhaseOperator.coeFn_compLpL f,
    scalarMultiplication_coe b.bounded
      ((onePhaseOperator - zeroPhaseOperator).compLpL 2 domainMeasure f),
    (onePhaseOperator - zeroPhaseOperator).coeFn_compLpL f] with q hadd hzero hscalar hdiff
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hzero, hscalar, hdiff]
  rfl

theorem coefficientOperator_lower (b : PhaseFraction) (q : Domain) (v : PhysicalGradient) :
    (1 / 4 : ℝ) * inner ℝ v v ≤ inner ℝ (coefficientOperator b q v) v := by
  rw [coefficientOperator_eq_matrix]
  have hpsd := mixture_lower (show b.value q ∈ Set.Icc (0 : ℝ) 1 from ⟨b.lower q, b.upper q⟩)
  have h : 0 ≤ inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ)
      (mixtureTensor (b.value q) - (1 / 4 : ℝ) • (1 : PhysicalTensor)) v) := by
    simpa only [Matrix.inner_toEuclideanCLM, star_trivial] using
      hpsd.dotProduct_mulVec_nonneg (v : Fin 2 × Fin 16 → ℝ)
  simp only [map_sub, map_smul, map_one, _root_.sub_apply,
    _root_.smul_apply, one_apply_eq_self,
    inner_sub_right, inner_smul_right] at h
  linarith [real_inner_comm v
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (mixtureTensor (b.value q)) v)]

theorem coefficientOperator_bound (b : PhaseFraction) (q : Domain) (v : PhysicalGradient) :
    ‖coefficientOperator b q v‖ ≤ 1 * ‖v‖ := by
  rw [coefficientOperator_eq_matrix]
  exact ((Matrix.toEuclideanCLM (𝕜 := ℝ) (mixtureTensor (b.value q))).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (mixture_opNorm_le ⟨b.lower q, b.upper q⟩) (norm_nonneg v))

theorem coefficientOperator_symmetric (b : PhaseFraction) (q : Domain)
    (v w : PhysicalGradient) :
    inner ℝ (coefficientOperator b q v) w = inner ℝ v (coefficientOperator b q w) := by
  have hsym : (coefficientOperator b q).IsSymmetric := by
    rw [coefficientOperator_eq_matrix]
    change (Matrix.toEuclideanCLM (𝕜 := ℝ) (mixtureTensor (b.value q)) :
      PhysicalGradient →ₗ[ℝ] PhysicalGradient).IsSymmetric
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (mixture_posSemidef ⟨b.lower q, b.upper q⟩).isHermitian
  exact hsym v w

theorem coefficientLaw_coercive (b : PhaseFraction) :
    CoerciveLaw (coefficientLaw b) (1 / 4) :=
  fieldLaw_coercive _ _ (coefficientLaw_coe b) _ (coefficientOperator_lower b)

theorem coefficientLaw_symmetric (b : PhaseFraction) : SymmetricLaw (coefficientLaw b) :=
  fieldLaw_symmetric _ _ (coefficientLaw_coe b) (coefficientOperator_symmetric b)

theorem coefficientLaw_norm_le (b : PhaseFraction) (f : PhysicalField) :
    ‖coefficientLaw b f‖ ≤ ‖f‖ := by
  simpa only [one_mul] using fieldLaw_norm_bound _ _ (coefficientLaw_coe b) 1
    (coefficientOperator_bound b) f

def effectiveOperator (b : PhaseFraction) : PhysicalGradient →L[ℝ] PhysicalGradient :=
  periodicEffective (coefficientLaw b) (1 / 4) (by norm_num) (coefficientLaw_coercive b)

def effectiveMatrix (b : PhaseFraction) : PhysicalTensor :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ)).symm (effectiveOperator b)

theorem effectiveMatrix_operator (b : PhaseFraction) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (effectiveMatrix b) = effectiveOperator b := by
  exact (Matrix.toEuclideanCLM (𝕜 := ℝ)).apply_symm_apply _

theorem effectiveOperator_cell_energy (b : PhaseFraction) (F : PhysicalGradient) :
    inner ℝ (effectiveOperator b F) F = sobolevCellEnergy (coefficientLaw b) F := by
  exact periodicEffective_energy _ (coefficientLaw_symmetric b) _ _ _ F

theorem coefficientLaw_energy (b : PhaseFraction) (f : PhysicalField) :
    inner ℝ (coefficientLaw b f) f =
      ∫ q, inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (mixtureTensor (b.value q)) (f q))
        (f q) ∂domainMeasure := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coefficientLaw_coe b f] with q hq
  rw [hq, coefficientOperator_eq_matrix]

end HierarchicalLaminates.Material
