module

public import HierarchicalLaminates.Composition.Counterexample
public import HierarchicalLaminates.Homogenization.ManuscriptTransport

/-! Exact-fraction composition on a period-2π cell. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.Composition

open MeasureTheory HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material
  HierarchicalLaminates.Lamination HierarchicalLaminates.Homogenization

theorem all_theta_counterexample_manuscript :
    ∀ θ : ℝ, 0 < θ → θ < 1 →
      ∃ b : PhaseFraction,
        Measurable (transportedIndicator b) ∧
        (∀ y : PeriodDomain manuscriptPeriod,
          transportedIndicator b y = 0 ∨ transportedIndicator b y = 1) ∧
        (∫ y, transportedIndicator b y ∂periodMeasure manuscriptPeriod) = θ ∧
        ((manuscriptPeriod ^ 2)⁻¹ *
          (∫ x in periodOpenCube manuscriptPeriod,
            transportedIndicator b (periodQuotient manuscriptPeriod x))) = θ ∧
        (∀ f : PeriodPhysicalField manuscriptPeriod,
          transportedLaw b f =ᵐ[periodMeasure manuscriptPeriod] fun y =>
            Matrix.toEuclideanCLM (𝕜 := ℝ) (mixtureTensor (transportedIndicator b y)) (f y)) ∧
        (∀ F : PhysicalGradient,
          quadraticEnergy (effectiveMatrix b) (F : Fin 2 × Fin 16 → ℝ) =
            periodWeakCellEnergy manuscriptPeriod (transportedLaw b) F) ∧
        0 < physicalLoadingDifference b ∧
        effectiveMatrix b ∉ closure (allFiniteLaminates phaseZero (phaseOne rho)) := by
  intro θ hθ₀ hθ₁
  obtain ⟨b, hb, hm, _he, hp, hn⟩ := all_theta_counterexample θ hθ₀ hθ₁
  exact ⟨b, transportedIndicator_measurable b, transportedIndicator_values b hb,
    (transportedIndicator_mean b).trans hm, (transportedIndicator_mean_openCube b).trans hm,
    transportedLaw_coe b, transported_cell_energy b, hp, hn⟩

end HierarchicalLaminates.Composition
