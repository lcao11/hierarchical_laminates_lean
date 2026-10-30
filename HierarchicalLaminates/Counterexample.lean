module

public import HierarchicalLaminates.Material.BinaryGap

/-!
# The phase-fraction one-half two-phase counterexample

The stripe indicator and the sixteen-potential constituents give a positive
difference of periodic weak-Sobolev cell energies. This separates the
effective tensor from the closure of finite laminates with arbitrary
directions, proportions and finite depths.
-/

@[expose] public section
noncomputable section

namespace HierarchicalLaminates

open MeasureTheory Periodic Material Lamination

theorem half_fraction_counterexample :
    ∃ N : ℕ, 2 ≤ N ∧
      (∀ q : Domain, Binary.binaryIndicator N q = 0 ∨ Binary.binaryIndicator N q = 1) ∧
      (∫ q, Binary.binaryIndicator N q ∂domainMeasure) = 1 / 2 ∧
      (∀ F : PhysicalGradient,
        quadraticEnergy (effectiveMatrix (binaryFraction N)) (F : Fin 2 × Fin 16 → ℝ) =
          sobolevCellEnergy (coefficientLaw (binaryFraction N)) F) ∧
      0 < physicalLoadingDifference (binaryFraction N) ∧
      effectiveMatrix (binaryFraction N) ∉
        closure (allFiniteLaminates phaseZero (phaseOne rho)) := by
  obtain ⟨N, _hN, hNtwo, hmean, hgap, hnot⟩ :=
    exists_binary_separation_of_bound binary_physical_gap_error
  exact ⟨N, hNtwo, Binary.binaryIndicator_values N, hmean,
    effectiveMatrix_quadratic_energy (binaryFraction N), hgap, hnot⟩

end HierarchicalLaminates
