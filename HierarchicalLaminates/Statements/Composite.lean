module

public import HierarchicalLaminates.GClosure.GeneralInclusion
public import HierarchicalLaminates.GClosure.DimensionPeriod

/-!
# The composite counterexample

The two constituents are chosen before the phase fraction. The witness is a
periodic binary coefficient on a period-2π cell, with the
conventional weak-Sobolev cell energy at every mean gradient.

The excluded laminate closure allows every real direction, proportion and
finite depth, including sequences with varying overall fractions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates

open MeasureTheory Periodic Material Lamination GClosure Homogenization

/-- A periodic binary material with fraction θ and effective tensor B.
The cell-energy equality uses weak H¹ potentials on the period-2π cell. -/
def IsPeriodicBinaryWitness {m : ℕ} (L₀ L₁ : Tensor (Fin m))
    (θ : ℝ) (B : Tensor (Fin m)) : Prop :=
  B.IsHermitian ∧ ∃ b : PhaseFraction,
    Measurable (transportedIndicator b) ∧
    (∀ y, transportedIndicator b y = 0 ∨ transportedIndicator b y = 1) ∧
    (manuscriptPeriod ^ 2)⁻¹ *
      (∫ x in periodOpenCube manuscriptPeriod,
        transportedIndicator b (periodQuotient manuscriptPeriod x)) = θ ∧
    ∀ F : Gradient (Fin m),
      quadraticEnergy B F =
        genericPeriodCellEnergy manuscriptPeriod L₀ L₁ b F

/-- Periodic binary composites exceed the full lamination
closure at every prescribed phase fraction 0 < θ < 1, for every number of potentials ≥ 16. -/
theorem composite_counterexample (m : ℕ) (hm : 16 ≤ m) :
    ∃ L₀ L₁ : Tensor (Fin m),
      L₀.PosDef ∧ L₁.PosDef ∧
      ∀ θ : ℝ, 0 < θ → θ < 1 →
        (laminationClosureAt L₀ L₁ θ ⊂ genericGClosure L₀ L₁ θ) ∧
        ∃ B : Tensor (Fin m),
          IsPeriodicBinaryWitness L₀ L₁ θ B ∧
          B ∉ closure (allFiniteLaminates L₀ L₁) := by
  refine ⟨dimensionPhaseZero m hm, dimensionPhaseOne m hm,
    dimensionPhaseZero_posDef m hm, dimensionPhaseOne_posDef m hm, ?_⟩
  intro θ hθ₀ hθ₁
  refine ⟨all_m_strict_inclusion m hm θ hθ₀ hθ₁, ?_⟩
  obtain ⟨b, hmeasurable, hbinary, hfraction, henergy, _hgap, houtside⟩ :=
    all_m_counterexample_manuscript m hm θ hθ₀ hθ₁
  have hselfadjoint : (dimensionEffective m hm b).IsHermitian :=
    reindexTensor_isHermitian (dimensionEquiv m hm)
      (extendTensor_isHermitian (effectiveMatrix_isHermitian b))
  exact ⟨dimensionEffective m hm b,
    ⟨hselfadjoint, b, hmeasurable, hbinary, hfraction, henergy⟩, houtside⟩

end HierarchicalLaminates
