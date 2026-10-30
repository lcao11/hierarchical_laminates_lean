module

public import HierarchicalLaminates.Composition.Composition

/-! The counterexample obtained through exact-fraction composition. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.Composition

open MeasureTheory HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material
  HierarchicalLaminates.Lamination HierarchicalLaminates.Homogenization

theorem all_theta_counterexample :
    ∀ θ : ℝ, 0 < θ → θ < 1 →
      ∃ b : PhaseFraction, IsBinary b ∧ phaseMean b = θ ∧
        (∀ F : PhysicalGradient,
          quadraticEnergy (effectiveMatrix b) (F : Fin 2 × Fin 16 → ℝ) =
            sobolevCellEnergy (coefficientLaw b) F) ∧
        0 < physicalLoadingDifference b ∧
        effectiveMatrix b ∉ closure (allFiniteLaminates phaseZero (phaseOne rho)) := by
  intro θ hθ₀ hθ₁
  obtain ⟨b, hb, hm, hp, hn⟩ := positive_binary_of_mem_GClosure
    (seed_composition_mem_GClosure θ hθ₀ hθ₁) (candidate_positive hθ₀ hθ₁)
  exact ⟨b, hb, hm, effectiveMatrix_quadratic_energy b, hp, hn⟩

end HierarchicalLaminates.Composition
