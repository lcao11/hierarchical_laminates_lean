module

public import HierarchicalLaminates.Composition.FourierApproximation
public import HierarchicalLaminates.Composition.MicroscopicResidual

/-! Arbitrarily accurate regular microscopic potentials and flux stream potentials. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.Composition

open HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material HierarchicalLaminates.WeakCalculus

/-- Each cell problem admits regular trial fields with arbitrarily small constitutive residual. -/
theorem exists_regular_microscopic_approx (b : PhaseFraction) (F : PhysicalGradient)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ u ψ : RegularPotential, ‖regularMicroscopicResidual b F u ψ‖ < ε := by
  obtain ⟨u, hu⟩ := exists_regular_gradient_approx (microscopicGradient b F)
    (microscopicGradient_mem b F) (ε / 3) (by positivity)
  obtain ⟨ψ, hψ⟩ := exists_regular_curl_approx
    (microscopicFlux b F - constantField (HierarchicalLaminates.Material.effectiveOperator b F))
    (centered_microscopicFlux_mean b F) (centered_microscopicFlux_orthogonal b F)
    (ε / 3) (by positivity)
  refine ⟨u, ψ, ?_⟩
  have h := regularMicroscopicResidual_bound b F u ψ hu.le hψ.le
  linarith

end HierarchicalLaminates.Composition
