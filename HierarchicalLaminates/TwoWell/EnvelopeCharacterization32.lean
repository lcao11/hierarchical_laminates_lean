module

public import HierarchicalLaminates.TwoWell.EnvelopeCharacterization
public import HierarchicalLaminates.TwoWell.Envelopes32

/-!
# Envelope characterizations on full `2 × 32` gradients

The split/join equivalence transports the periodic Jensen predicate and all its
real-valued minorants between paired gradients and full `2 × 32` gradients.
Continuity and nonnegativity of the two-well energy give its greatest periodic
minorant and comparison with the rank-one convex envelope.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.TwoWell

theorem twoWell_quasiconvexEnvelope32_eq (F : Gradient32) :
    quasiconvexEnvelope32 twoWellEnergy32 F =
      quasiconvexEnvelope twoWellEnergy (split32 F) := by
  simpa only [join32_split32] using twoWell_quasiconvexEnvelope32 (split32 F)

theorem twoWell_rankOneEnvelope32_eq (F : Gradient32) :
    rankOneEnvelope32 twoWellEnergy32 F =
      rankOneEnvelope twoWellEnergy (split32 F) := by
  simpa only [join32_split32] using twoWell_rankOneEnvelope32 (split32 F)

theorem twoWell_periodicQuasiconvex32_rankOneConvex32 {h : Gradient32 → ℝ}
    (hh : PeriodicQuasiconvex32 h) (hle : ∀ F, h F ≤ twoWellEnergy32 F) :
    RankOneConvex32 h := by
  apply (rankOne32_pullback h).2
  apply twoWell_periodicQuasiconvex_rankOneConvex ((quasiconvex32_pullback h).1 hh)
  intro F
  simpa only [twoWellEnergy32_join32] using hle (join32 F)

theorem twoWell_quasiconvexEnvelope32_periodicQuasiconvex32 :
    PeriodicQuasiconvex32 (quasiconvexEnvelope32 twoWellEnergy32) := by
  have heq : quasiconvexEnvelope32 twoWellEnergy32 =
      fun F => quasiconvexEnvelope twoWellEnergy (split32 F) :=
    funext twoWell_quasiconvexEnvelope32_eq
  rw [heq]
  exact (quasiconvex32_pushforward (quasiconvexEnvelope twoWellEnergy)).1
    (quasiconvexEnvelope_periodicQuasiconvex twoWellEnergy_nonneg twoWellEnergy_continuous)

theorem twoWell_quasiconvexEnvelope32_isGreatest :
    IsGreatest {h : Gradient32 → ℝ | PeriodicQuasiconvex32 h ∧ ∀ F, h F ≤ twoWellEnergy32 F}
      (quasiconvexEnvelope32 twoWellEnergy32) := by
  refine ⟨⟨twoWell_quasiconvexEnvelope32_periodicQuasiconvex32,?_⟩,?_⟩
  · intro F
    rw [twoWell_quasiconvexEnvelope32_eq,twoWellEnergy32_eq]
    exact quasiconvexEnvelope_le_energy twoWellEnergy_nonneg (split32 F)
  · intro h hh F
    rw [twoWell_quasiconvexEnvelope32_eq]
    have hbelow : ∀ G, h (join32 G) ≤ twoWellEnergy G := by
      intro G
      simpa only [twoWellEnergy32_join32] using hh.2 (join32 G)
    simpa only [join32_split32] using le_quasiconvexEnvelope
      ⟨(quasiconvex32_pullback h).1 hh.1,hbelow⟩ (split32 F)

theorem twoWell_quasiconvexEnvelope32_le_rankOneEnvelope32 (F : Gradient32) :
    quasiconvexEnvelope32 twoWellEnergy32 F ≤ rankOneEnvelope32 twoWellEnergy32 F := by
  rw [twoWell_quasiconvexEnvelope32_eq,twoWell_rankOneEnvelope32_eq]
  exact twoWell_quasiconvexEnvelope_le_rankOneEnvelope (split32 F)

end HierarchicalLaminates.TwoWell
