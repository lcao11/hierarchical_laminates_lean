module

public import HierarchicalLaminates.Homogenization.ConventionalClosure
public import HierarchicalLaminates.Periodic.Rescaling

/-! Transport of binary fractions to a period-2π cell. -/

@[expose] public section
noncomputable section

namespace HierarchicalLaminates.Homogenization

open MeasureTheory HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material HierarchicalLaminates.Lamination

def transportedIndicator (b : PhaseFraction) (y : PeriodDomain manuscriptPeriod) : ℝ :=
  b.value ((scaleTorus manuscriptPeriod).symm y)

def transportedLaw (b : PhaseFraction) :
    PeriodPhysicalField manuscriptPeriod →L[ℝ] PeriodPhysicalField manuscriptPeriod :=
  rescaledLaw manuscriptPeriod (coefficientLaw b)

theorem transportedIndicator_measurable (b : PhaseFraction) : Measurable (transportedIndicator b) :=
  b.measurable.comp (scaleTorus manuscriptPeriod).symm.measurable

theorem transportedIndicator_values (b : PhaseFraction) (hb : IsBinary b)
    (y : PeriodDomain manuscriptPeriod) :
    transportedIndicator b y = 0 ∨ transportedIndicator b y = 1 := hb _

theorem transportedIndicator_mean (b : PhaseFraction) :
    (∫ y, transportedIndicator b y ∂periodMeasure manuscriptPeriod) = phaseMean b :=
  integral_unscaling manuscriptPeriod b.value

theorem transportedIndicator_integrable_volume (b : PhaseFraction) :
    Integrable (transportedIndicator b) (volume : Measure (PeriodDomain manuscriptPeriod)) := by
  apply Integrable.of_bound (transportedIndicator_measurable b).aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro y
  change ‖b.value ((scaleTorus manuscriptPeriod).symm y)‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (b.lower _)]
  exact b.upper _

theorem transportedIndicator_mean_openCube (b : PhaseFraction) :
    (manuscriptPeriod ^ 2)⁻¹ *
        (∫ x in periodOpenCube manuscriptPeriod,
          transportedIndicator b (periodQuotient manuscriptPeriod x)) = phaseMean b := by
  rw [← transportedIndicator_mean b]
  exact (normalized_period_integral_eq_openCube manuscriptPeriod (transportedIndicator b)
    (transportedIndicator_integrable_volume b)).symm

theorem transportedLaw_coe (b : PhaseFraction) (f : PeriodPhysicalField manuscriptPeriod) :
    transportedLaw b f =ᵐ[periodMeasure manuscriptPeriod] fun y =>
      Matrix.toEuclideanCLM (𝕜 := ℝ) (mixtureTensor (transportedIndicator b y)) (f y) := by
  have h := rescaledLaw_coe manuscriptPeriod (coefficientLaw b)
    (fun q v => coefficientOperator b q v) (coefficientLaw_coe b) f
  filter_upwards [h] with y hy
  exact hy.trans (congrArg (fun T : PhysicalGradient →L[ℝ] PhysicalGradient => T (f y))
    (coefficientOperator_eq_matrix b ((scaleTorus manuscriptPeriod).symm y)))

theorem transported_cell_energy (b : PhaseFraction) (F : PhysicalGradient) :
    quadraticEnergy (effectiveMatrix b) (F : Fin 2 × Fin 16 → ℝ) =
      periodWeakCellEnergy manuscriptPeriod (transportedLaw b) F :=
  (effectiveMatrix_quadratic_energy b F).trans
    (rescaledLaw_cellEnergy manuscriptPeriod (coefficientLaw b) F).symm

end HierarchicalLaminates.Homogenization
