module

public import HierarchicalLaminates.Statements.TwoWell
public import HierarchicalLaminates.TwoWell.PeriodTransport

/-!
# The two-well envelope gap at any positive period

The full `2 × 32` energy formed by the minimum of two positive-definite
quadratic forms has distinct periodic quasiconvex and rank-one convex
envelopes. Nonlinear period transport gives the gap for every `L > 0`,
including the period-`2π` cell.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates

open Lamination TwoWell

/-- The two quadratic forms from the construction give an envelope gap at every `L > 0`. -/
theorem two_well_energy_gap_period (L : ℝ) [Fact (0 < L)] :
    ∃ A₀ A₁ : Tensor (Fin 32),
      A₀.PosDef ∧ A₁.PosDef ∧
      ∃ F : Gradient (Fin 32),
        periodQuasiconvexEnvelope32 L
            (fun G => min (quadraticEnergy A₀ G) (quadraticEnergy A₁ G)) F <
          rankOneEnvelope32
            (fun G => min (quadraticEnergy A₀ G) (quadraticEnergy A₁ G)) F := by
  simpa only [periodQuasiconvexEnvelope32_eq] using two_well_energy_gap

/-- The envelope gap on the period-`2π` cell with normalized cell measure. -/
theorem two_well_energy_gap_manuscript :
    ∃ A₀ A₁ : Tensor (Fin 32),
      A₀.PosDef ∧ A₁.PosDef ∧
      ∃ F : Gradient (Fin 32),
        periodQuasiconvexEnvelope32 manuscriptPeriod
            (fun G => min (quadraticEnergy A₀ G) (quadraticEnergy A₁ G)) F <
          rankOneEnvelope32
            (fun G => min (quadraticEnergy A₀ G) (quadraticEnergy A₁ G)) F :=
  two_well_energy_gap_period manuscriptPeriod

end HierarchicalLaminates
