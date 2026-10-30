module

public import HierarchicalLaminates.TwoWell.Envelopes32
public import HierarchicalLaminates.TwoWell.SobolevEnvelopes

/-! The periodic weak-H¹ Jensen envelope on the full 32-potential space. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.TwoWell

open MeasureTheory HierarchicalLaminates.Periodic

def weakTrial32 (F : Gradient32) (u v : SobolevPotential) (q : Domain) : Gradient32 :=
  join32 (weakTrial (split32 F) u v q)

def SobolevQuasiconvex32 (h : Gradient32 → ℝ) : Prop :=
  ∀ (F : Gradient32) (u v : SobolevPotential),
    Integrable (fun q => h (weakTrial32 F u v q)) domainMeasure ∧
      h F ≤ ∫ q, h (weakTrial32 F u v q) ∂domainMeasure

def sobolevQuasiconvexEnvelope32 (W : Gradient32 → ℝ) (F : Gradient32) : ℝ :=
  sSup ((fun h => h F) '' {h | SobolevQuasiconvex32 h ∧ ∀ G, h G ≤ W G})

theorem sobolev32_pullback (h : Gradient32 → ℝ) :
    SobolevQuasiconvex32 h ↔ SobolevQuasiconvex (fun F => h (join32 F)) := by
  constructor
  · intro hh F u v
    simpa only [weakTrial32,split32_join32] using hh (join32 F) u v
  · intro hh F u v
    simpa only [weakTrial32,join32_split32] using hh (split32 F) u v

theorem sobolev32_pushforward (h : PairedGradient → ℝ) :
    SobolevQuasiconvex h ↔ SobolevQuasiconvex32 (fun F => h (split32 F)) := by
  rw [sobolev32_pullback]
  simp only [split32_join32]

theorem sobolevQuasiconvexEnvelope32_transport (W : Gradient32 → ℝ) (F : Gradient32) :
    sobolevQuasiconvexEnvelope32 W F =
      sobolevQuasiconvexEnvelope (fun G => W (join32 G)) (split32 F) := by
  apply congrArg sSup
  ext r
  constructor
  · rintro ⟨h,⟨hc,hb⟩,hr⟩
    refine ⟨(fun G => h (join32 G)),⟨(sobolev32_pullback h).1 hc,?_⟩,?_⟩
    · exact fun G => hb (join32 G)
    · simpa only [join32_split32] using hr
  · rintro ⟨h,⟨hc,hb⟩,hr⟩
    refine ⟨(fun G => h (split32 G)),⟨(sobolev32_pushforward h).1 hc,?_⟩,hr⟩
    intro G
    simpa only [join32_split32] using hb (split32 G)

theorem sobolev32Envelope_le_periodic32Envelope {W : Gradient32 → ℝ}
    (hW : ∀ F, 0 ≤ W F) (F : Gradient32) :
    sobolevQuasiconvexEnvelope32 W F ≤ quasiconvexEnvelope32 W F := by
  rw [sobolevQuasiconvexEnvelope32_transport,quasiconvexEnvelope32_transport]
  exact sobolevEnvelope_le_periodicEnvelope (fun G => hW (join32 G)) _

end HierarchicalLaminates.TwoWell
