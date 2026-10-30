module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Normalized periodic L² fields

The mean map is the adjoint of the constant-field embedding and equals the
Bochner integral. The domain carries normalized Haar measure, as in the
unit-torus Fourier theory.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Periodic

open MeasureTheory
open scoped ENNReal

abbrev Domain := UnitAddTorus (Fin 2)

def domainMeasure : Measure Domain :=
  Measure.pi (fun _ : Fin 2 => AddCircle.haarAddCircle (T := (1 : ℝ)))

instance domainMeasure_probability : IsProbabilityMeasure domainMeasure := by
  dsimp [domainMeasure]
  infer_instance

abbrev Field (E : Type*) [NormedAddCommGroup E] :=
  Lp E 2 domainMeasure

abbrev ScalarField := Field ℝ

abbrev PhysicalGradient := EuclideanSpace ℝ (Fin 2 × Fin 16)

abbrev PhysicalField := Field PhysicalGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def constantField : E →L[ℝ] Field E := Lp.constL 2 domainMeasure ℝ

@[simp]
theorem constantField_apply (F : E) : constantField F = Lp.const 2 domainMeasure F := rfl

theorem constantField_norm (F : E) : ‖constantField F‖ = ‖F‖ := by
  simp [constantField, Lp.norm_const, measureReal_def]

theorem constantField_opNorm_le : ‖(constantField : E →L[ℝ] Field E)‖ ≤ 1 := by
  simpa [constantField, measureReal_def] using (Lp.norm_constL_le (E := E) (p := 2) (μ := domainMeasure) ℝ)

variable [CompleteSpace E]

def meanField : Field E →L[ℝ] E := (constantField : E →L[ℝ] Field E).adjoint

theorem constant_mean_pairing (F : E) (v : Field E) :
    inner ℝ (constantField F) v = inner ℝ F (meanField v) := by
  exact ((constantField : E →L[ℝ] Field E).adjoint_inner_right F v).symm

theorem constantField_inner_eq_integral (F : E) (v : Field E) :
    inner ℝ (constantField F) v = inner ℝ F (∫ x, v x ∂domainMeasure) := by
  have h := MeasureTheory.L2.inner_indicatorConstLp_eq_inner_setIntegral
    (𝕜 := ℝ) (μ := domainMeasure) MeasurableSet.univ
      (measure_ne_top _ _) F v
  simpa only [indicatorConstLp_univ, constantField_apply, Measure.restrict_univ] using h

theorem meanField_eq_integral (v : Field E) : meanField v = ∫ x, v x ∂domainMeasure := by
  apply ext_inner_left ℝ
  intro F
  exact (constant_mean_pairing F v).symm.trans (constantField_inner_eq_integral F v)

theorem meanField_opNorm_le : ‖(meanField : Field E →L[ℝ] E)‖ ≤ 1 := by
  calc
    ‖(meanField : Field E →L[ℝ] E)‖ = ‖(constantField : E →L[ℝ] Field E)‖ :=
      ContinuousLinearMap.adjoint.norm_map _
    _ ≤ 1 := constantField_opNorm_le

theorem meanField_norm_le (v : Field E) : ‖meanField v‖ ≤ ‖v‖ := by
  calc
    ‖meanField v‖ ≤ ‖(meanField : Field E →L[ℝ] E)‖ * ‖v‖ :=
      (meanField : Field E →L[ℝ] E).le_opNorm v
    _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right meanField_opNorm_le (norm_nonneg _)
    _ = ‖v‖ := one_mul _

@[simp]
theorem mean_constantField (F : E) : meanField (constantField F) = F := by
  rw [meanField_eq_integral]
  calc
    (∫ x : Domain, (constantField F) x ∂domainMeasure) = ∫ _ : Domain, F ∂domainMeasure :=
      integral_congr_ae (Lp.coeFn_const 2 domainMeasure F)
    _ = F := by simp [measureReal_def]

def continuousField : C(Domain, E) →L[ℝ] Field E :=
  ContinuousMap.toLp 2 domainMeasure ℝ

def meanContinuous : C(Domain, E) →L[ℝ] E := meanField.comp continuousField

theorem meanContinuous_eq_integral (f : C(Domain, E)) :
    meanContinuous f = ∫ x, f x ∂domainMeasure := by
  change meanField (continuousField f) = _
  rw [meanField_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure f)

omit [CompleteSpace E] in
@[simp]
theorem continuousField_const (c : E) :
    continuousField (ContinuousMap.const Domain c) = constantField c := by
  apply Lp.ext
  exact (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure _).trans
    (Lp.coeFn_const 2 domainMeasure c).symm

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem field_integrable (v : Field E) : Integrable v domainMeasure := by
  have h := integrableOn_Lp_of_measure_ne_top v
    (show (1 : ℝ≥0∞) ≤ 2 by norm_num) (measure_ne_top domainMeasure Set.univ)
  simpa only [IntegrableOn, Measure.restrict_univ] using h

theorem meanField_comp {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] (L : E →L[ℝ] F) (v : Field E) :
    meanField (L.compLpL 2 domainMeasure v) = L (meanField v) := by
  rw [meanField_eq_integral, meanField_eq_integral]
  calc
    (∫ x, L.compLpL 2 domainMeasure v x ∂domainMeasure) =
        ∫ x, L (v x) ∂domainMeasure := integral_congr_ae (L.coeFn_compLpL v)
    _ = L (∫ x, v x ∂domainMeasure) := L.integral_comp_comm (field_integrable v)

end HierarchicalLaminates.Periodic
