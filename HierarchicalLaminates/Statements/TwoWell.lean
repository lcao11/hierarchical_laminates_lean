module

public import HierarchicalLaminates.TwoWell.Gap
public import HierarchicalLaminates.TwoWell.Envelopes32

/-!
# Separation of the two-well energy envelopes

Two positive-definite quadratic forms on gradients of thirty-two scalar
potentials have a minimum whose quasiconvex and rank-one convex envelopes
differ. The tensor representation makes each quadratic form explicit as
the usual gradient–tensor–gradient pairing.

The detailed minorant, quantitative gap and periodic trial inequalities
are established in the supporting TwoWell modules.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates

open Lamination Material TwoWell

/-- The two-well theorem: a strict envelope gap on the full 2 × 32 gradient space. -/
theorem two_well_energy_gap :
    ∃ A₀ A₁ : Tensor (Fin 32),
      A₀.PosDef ∧ A₁.PosDef ∧
      ∃ F : Gradient (Fin 32),
        quasiconvexEnvelope32
            (fun G => min (quadraticEnergy A₀ G) (quadraticEnergy A₁ G)) F <
          rankOneEnvelope32
            (fun G => min (quadraticEnergy A₀ G) (quadraticEnergy A₁ G)) F := by
  obtain ⟨N, _hN, _hbinary, _hmean, _hloading, hgap, _hquantitative⟩ := two_well_gap
  refine ⟨branchTensor32 phaseZero, branchTensor32 (phaseOne rho),
    branches32_posDef.1, branches32_posDef.2,
    join32 (applicationMean (binaryFraction N)), ?_⟩
  change quasiconvexEnvelope32 twoWellEnergy32 _ <
    rankOneEnvelope32 twoWellEnergy32 _
  simpa only [twoWell_quasiconvexEnvelope32, twoWell_rankOneEnvelope32] using hgap

end HierarchicalLaminates
