module

public import HierarchicalLaminates.Counterexample
public import HierarchicalLaminates.Periodic.Rescaling

/-!
# The two-phase counterexample on a period-2π cell

Multiplying coordinates and potential values by `2π` preserves the gradient
and normalized cell energy. The transported indicator has the same phase
fraction, and the period-cell weak derivatives satisfy integration by parts.
-/

@[expose] public section
noncomputable section

namespace HierarchicalLaminates

open MeasureTheory Periodic Material Lamination

abbrev manuscriptPeriod : ℝ := 2 * Real.pi

instance manuscriptPeriod_positive : Fact (0 < manuscriptPeriod) := ⟨by positivity⟩

def manuscriptIndicator (N : ℕ) (y : PeriodDomain manuscriptPeriod) : ℝ :=
  Binary.binaryIndicator N ((scaleTorus manuscriptPeriod).symm y)

def manuscriptCoefficientLaw (N : ℕ) :
    PeriodPhysicalField manuscriptPeriod →L[ℝ] PeriodPhysicalField manuscriptPeriod :=
  rescaledLaw manuscriptPeriod (coefficientLaw (binaryFraction N))

theorem manuscriptIndicator_measurable (N : ℕ) : Measurable (manuscriptIndicator N) :=
  (Binary.binaryIndicator_measurable N).comp (scaleTorus manuscriptPeriod).symm.measurable

theorem manuscriptIndicator_values (N : ℕ) (y : PeriodDomain manuscriptPeriod) :
    manuscriptIndicator N y = 0 ∨ manuscriptIndicator N y = 1 :=
  Binary.binaryIndicator_values N _

theorem manuscriptIndicator_real_coordinates (N : ℕ) (x : Fin 2 → ℝ) :
    manuscriptIndicator N (fun i => (x i : AddCircle manuscriptPeriod)) =
      Binary.binaryIndicator N (fun i => (x i / manuscriptPeriod : UnitAddCircle)) := by
  unfold manuscriptIndicator
  rw [scaleTorus_symm_coe]

theorem manuscriptIndicator_mean (N : ℕ) :
    (∫ y, manuscriptIndicator N y ∂periodMeasure manuscriptPeriod) =
      ∫ q, Binary.binaryIndicator N q ∂domainMeasure :=
  integral_unscaling manuscriptPeriod (Binary.binaryIndicator N)

theorem manuscriptIndicator_integrable_volume (N : ℕ) :
    Integrable (manuscriptIndicator N) (volume : Measure (PeriodDomain manuscriptPeriod)) := by
  apply Integrable.of_bound (manuscriptIndicator_measurable N).aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro y
  rcases manuscriptIndicator_values N y with hy | hy <;> simp [hy]

theorem manuscriptIndicator_mean_openCube (N : ℕ) :
    (manuscriptPeriod ^ 2)⁻¹ *
        (∫ x in periodOpenCube manuscriptPeriod,
          manuscriptIndicator N (periodQuotient manuscriptPeriod x)) =
      ∫ q, Binary.binaryIndicator N q ∂domainMeasure := by
  rw [← manuscriptIndicator_mean N]
  exact (normalized_period_integral_eq_openCube manuscriptPeriod (manuscriptIndicator N)
    (manuscriptIndicator_integrable_volume N)).symm

theorem manuscriptCoefficientLaw_coe (N : ℕ) (f : PeriodPhysicalField manuscriptPeriod) :
    manuscriptCoefficientLaw N f =ᵐ[periodMeasure manuscriptPeriod] fun y =>
      Matrix.toEuclideanCLM (𝕜 := ℝ) (mixtureTensor (manuscriptIndicator N y)) (f y) := by
  have h := rescaledLaw_coe manuscriptPeriod (coefficientLaw (binaryFraction N))
    (fun q v => coefficientOperator (binaryFraction N) q v)
    (coefficientLaw_coe (binaryFraction N)) f
  filter_upwards [h] with y hy
  exact hy.trans (congrArg (fun T : PhysicalGradient →L[ℝ] PhysicalGradient => T (f y))
    (coefficientOperator_eq_matrix (binaryFraction N) ((scaleTorus manuscriptPeriod).symm y)))

theorem manuscript_cell_energy (N : ℕ) (F : PhysicalGradient) :
    quadraticEnergy (effectiveMatrix (binaryFraction N)) (F : Fin 2 × Fin 16 → ℝ) =
      periodWeakCellEnergy manuscriptPeriod (manuscriptCoefficientLaw N) F :=
  (effectiveMatrix_quadratic_energy (binaryFraction N) F).trans
    (rescaledLaw_cellEnergy manuscriptPeriod (coefficientLaw (binaryFraction N)) F).symm

theorem half_fraction_counterexample_manuscript :
    ∃ N : ℕ, 2 ≤ N ∧
      Measurable (manuscriptIndicator N) ∧
      (∀ y : PeriodDomain manuscriptPeriod,
        manuscriptIndicator N y = 0 ∨ manuscriptIndicator N y = 1) ∧
      (∫ y, manuscriptIndicator N y ∂periodMeasure manuscriptPeriod) = 1 / 2 ∧
      ((manuscriptPeriod ^ 2)⁻¹ *
        (∫ x in periodOpenCube manuscriptPeriod,
          manuscriptIndicator N (periodQuotient manuscriptPeriod x))) = 1 / 2 ∧
      (∀ f : PeriodPhysicalField manuscriptPeriod,
        manuscriptCoefficientLaw N f =ᵐ[periodMeasure manuscriptPeriod] fun y =>
          Matrix.toEuclideanCLM (𝕜 := ℝ) (mixtureTensor (manuscriptIndicator N y)) (f y)) ∧
      (∀ F : PhysicalGradient,
        quadraticEnergy (effectiveMatrix (binaryFraction N)) (F : Fin 2 × Fin 16 → ℝ) =
          periodWeakCellEnergy manuscriptPeriod (manuscriptCoefficientLaw N) F) ∧
      0 < physicalLoadingDifference (binaryFraction N) ∧
      effectiveMatrix (binaryFraction N) ∉
        closure (allFiniteLaminates phaseZero (phaseOne rho)) := by
  obtain ⟨N, hN, _hbool, hmean, _henergy, hgap, hnot⟩ := half_fraction_counterexample
  refine ⟨N, hN, manuscriptIndicator_measurable N, manuscriptIndicator_values N, ?_,
    ?_, manuscriptCoefficientLaw_coe N, manuscript_cell_energy N, hgap, hnot⟩
  · exact (manuscriptIndicator_mean N).trans hmean
  · exact (manuscriptIndicator_mean_openCube N).trans hmean

end HierarchicalLaminates
