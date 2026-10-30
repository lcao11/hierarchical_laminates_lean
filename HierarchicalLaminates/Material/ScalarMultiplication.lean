module

public import HierarchicalLaminates.Periodic.FieldSpace
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Tactic.Linarith

/-!
# Bounded measurable multiplication on the normalized periodic L² space
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Material

open MeasureTheory
open HierarchicalLaminates.Periodic
open scoped ENNReal

structure BoundedScalar where
  value : Domain → ℝ
  measurable : Measurable value
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  abs_le : ∀ q, |value q| ≤ bound

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem scalar_product_memLp (b : BoundedScalar) (f : Periodic.Field E) :
    MemLp (fun q => b.value q • f q) 2 domainMeasure := by
  have hb : MemLp b.value ∞ domainMeasure :=
    memLp_top_of_bound b.measurable.aestronglyMeasurable b.bound
      (Filter.Eventually.of_forall (fun q => by simpa only [Real.norm_eq_abs] using b.abs_le q))
  exact hb.smul (Lp.memLp f)

def scalarProduct (b : BoundedScalar) (f : Periodic.Field E) : Periodic.Field E :=
  (scalar_product_memLp b f).toLp (fun q => b.value q • f q)

omit [CompleteSpace E] in
theorem scalarProduct_coe (b : BoundedScalar) (f : Periodic.Field E) :
    scalarProduct b f =ᵐ[domainMeasure] fun q => b.value q • f q :=
  MemLp.coeFn_toLp (scalar_product_memLp b f)

theorem scalarProduct_add (b : BoundedScalar) (f g : Periodic.Field E) :
    scalarProduct b (f + g) = scalarProduct b f + scalarProduct b g := by
  apply Lp.ext
  filter_upwards [scalarProduct_coe b (f + g), scalarProduct_coe b f,
    scalarProduct_coe b g, Lp.coeFn_add f g,
    Lp.coeFn_add (scalarProduct b f) (scalarProduct b g)] with q hl hf hg hsum hout
  simp only [hl, hout, hf, hg, hsum, Pi.add_apply, smul_add]

theorem scalarProduct_smul (b : BoundedScalar) (r : ℝ) (f : Periodic.Field E) :
    scalarProduct b (r • f) = r • scalarProduct b f := by
  apply Lp.ext
  filter_upwards [scalarProduct_coe b (r • f), scalarProduct_coe b f,
    Lp.coeFn_smul r f, Lp.coeFn_smul r (scalarProduct b f)] with q hl hf hin hout
  simp only [hl, hout, hf, hin, Pi.smul_apply, smul_smul, mul_comm]

def scalarMultiplicationLinear (b : BoundedScalar) : Periodic.Field E →ₗ[ℝ] Periodic.Field E where
  toFun := scalarProduct b
  map_add' := scalarProduct_add b
  map_smul' := scalarProduct_smul b

theorem scalarProduct_norm_le (b : BoundedScalar) (f : Periodic.Field E) :
    ‖scalarProduct b f‖ ≤ b.bound * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [scalarProduct_coe b f] with q hq
  rw [hq, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (b.abs_le q) (norm_nonneg _)

def scalarMultiplication (b : BoundedScalar) : Periodic.Field E →L[ℝ] Periodic.Field E :=
  (scalarMultiplicationLinear b).mkContinuous b.bound (scalarProduct_norm_le b)

theorem scalarMultiplication_norm_le (b : BoundedScalar) :
    ‖(scalarMultiplication b : Periodic.Field E →L[ℝ] Periodic.Field E)‖ ≤ b.bound :=
  LinearMap.mkContinuous_norm_le _ b.bound_nonneg _

theorem scalarMultiplication_coe (b : BoundedScalar) (f : Periodic.Field E) :
    scalarMultiplication b f =ᵐ[domainMeasure] fun q => b.value q • f q :=
  scalarProduct_coe b f

theorem scalarMultiplication_symmetric (b : BoundedScalar) (f g : Periodic.Field E) :
    inner ℝ (scalarMultiplication b f) g = inner ℝ f (scalarMultiplication b g) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [scalarMultiplication_coe b f, scalarMultiplication_coe b g] with q hf hg
  rw [hf, hg, real_inner_smul_left, real_inner_smul_right]

end HierarchicalLaminates.Material
