module

public import HierarchicalLaminates.TwoWell.Components32

/-! Periodic Jensen and rank-one convex envelopes on all 2 by 32 gradients. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.TwoWell

open MeasureTheory HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Lamination
  HierarchicalLaminates.Composition

def RankOneConvex32 (h : Gradient32 → ℝ) : Prop :=
  ∀ (F₁ F₂ : Gradient32), Compatible32 F₁ F₂ → ∀ a : LayerProportion,
    h ((a : ℝ) • F₁+(1-(a : ℝ)) • F₂) ≤
      (a : ℝ)*h F₁+(1-(a : ℝ))*h F₂

/-- Joining the two arbitrary C¹ potential blocks is a 32-potential variation. -/
def regularTrial32 (F : Gradient32) (u v : RegularPotential) (q : Domain) : Gradient32 :=
  join32 (regularTrial (split32 F) u v q)

def PeriodicQuasiconvex32 (h : Gradient32 → ℝ) : Prop :=
  ∀ (F : Gradient32) (u v : RegularPotential),
    Integrable (fun q => h (regularTrial32 F u v q)) domainMeasure ∧
      h F ≤ ∫ q, h (regularTrial32 F u v q) ∂domainMeasure

def rankOneEnvelope32 (W : Gradient32 → ℝ) (F : Gradient32) : ℝ :=
  sSup ((fun h => h F) '' {h | RankOneConvex32 h ∧ ∀ G, h G ≤ W G})

def quasiconvexEnvelope32 (W : Gradient32 → ℝ) (F : Gradient32) : ℝ :=
  sSup ((fun h => h F) '' {h | PeriodicQuasiconvex32 h ∧ ∀ G, h G ≤ W G})

theorem rankOne32_pullback (h : Gradient32 → ℝ) :
    RankOneConvex32 h ↔ RankOneConvex (fun F => h (join32 F)) := by
  constructor
  · intro hh F₁ F₂ hc a
    have hcomp : Compatible32 (join32 F₁) (join32 F₂) :=
      (compatible32_iff _ _).2 (by simpa only [split32_join32] using hc)
    simpa only [join32_add,join32_smul] using hh _ _ hcomp a
  · intro hh F₁ F₂ hc a
    simpa only [join32_add,join32_smul,join32_split32] using
      hh (split32 F₁) (split32 F₂) ((compatible32_iff _ _).1 hc) a

theorem quasiconvex32_pullback (h : Gradient32 → ℝ) :
    PeriodicQuasiconvex32 h ↔ PeriodicQuasiconvex (fun F => h (join32 F)) := by
  constructor
  · intro hh F u v
    simpa only [regularTrial32,split32_join32] using hh (join32 F) u v
  · intro hh F u v
    simpa only [regularTrial32,join32_split32] using hh (split32 F) u v

theorem rankOne32_pushforward (h : PairedGradient → ℝ) :
    RankOneConvex h ↔ RankOneConvex32 (fun F => h (split32 F)) := by
  rw [rankOne32_pullback]
  simp only [split32_join32]

theorem quasiconvex32_pushforward (h : PairedGradient → ℝ) :
    PeriodicQuasiconvex h ↔ PeriodicQuasiconvex32 (fun F => h (split32 F)) := by
  rw [quasiconvex32_pullback]
  simp only [split32_join32]

theorem rankOneEnvelope32_transport (W : Gradient32 → ℝ) (F : Gradient32) :
    rankOneEnvelope32 W F =
      rankOneEnvelope (fun G => W (join32 G)) (split32 F) := by
  apply congrArg sSup
  ext r
  constructor
  · rintro ⟨h,⟨hc,hb⟩,hr⟩
    refine ⟨(fun G => h (join32 G)),⟨(rankOne32_pullback h).1 hc,?_⟩,?_⟩
    · exact fun G => hb (join32 G)
    · simpa only [join32_split32] using hr
  · rintro ⟨h,⟨hc,hb⟩,hr⟩
    refine ⟨(fun G => h (split32 G)),⟨(rankOne32_pushforward h).1 hc,?_⟩,hr⟩
    intro G
    simpa only [join32_split32] using hb (split32 G)

theorem quasiconvexEnvelope32_transport (W : Gradient32 → ℝ) (F : Gradient32) :
    quasiconvexEnvelope32 W F =
      quasiconvexEnvelope (fun G => W (join32 G)) (split32 F) := by
  apply congrArg sSup
  ext r
  constructor
  · rintro ⟨h,⟨hc,hb⟩,hr⟩
    refine ⟨(fun G => h (join32 G)),⟨(quasiconvex32_pullback h).1 hc,?_⟩,?_⟩
    · exact fun G => hb (join32 G)
    · simpa only [join32_split32] using hr
  · rintro ⟨h,⟨hc,hb⟩,hr⟩
    refine ⟨(fun G => h (split32 G)),⟨(quasiconvex32_pushforward h).1 hc,?_⟩,hr⟩
    intro G
    simpa only [join32_split32] using hb (split32 G)

theorem twoWellEnergy32_join32 (F : PairedGradient) :
    twoWellEnergy32 (join32 F) = twoWellEnergy F := by
  rw [twoWellEnergy32_eq,split32_join32]

theorem twoWell_rankOneEnvelope32 (F : PairedGradient) :
    rankOneEnvelope32 twoWellEnergy32 (join32 F) = rankOneEnvelope twoWellEnergy F := by
  rw [rankOneEnvelope32_transport,split32_join32]
  simp only [twoWellEnergy32_join32]

theorem twoWell_quasiconvexEnvelope32 (F : PairedGradient) :
    quasiconvexEnvelope32 twoWellEnergy32 (join32 F) = quasiconvexEnvelope twoWellEnergy F := by
  rw [quasiconvexEnvelope32_transport,split32_join32]
  simp only [twoWellEnergy32_join32]

end HierarchicalLaminates.TwoWell
