module

public import HierarchicalLaminates.TwoWell.Base
public import HierarchicalLaminates.Composition.RegularPotential

/-! Periodic Jensen quasiconvexity, rank-one convexity and minorant envelopes. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.TwoWell

open MeasureTheory HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Lamination
  HierarchicalLaminates.Composition

/-- Periodic C¹ potential variations in the two independent blocks. -/
def regularTrial (F : PairedGradient) (u v : RegularPotential) (q : Domain) :
    PairedGradient :=
  (F.1 + (fun c => u.gradient q c), F.2 + (fun c => v.gradient q c))

/-- Quasiconvexity in the periodic Jensen sense, including integrability of
the energy for every C¹ potential variation. -/
def PeriodicQuasiconvex (h : PairedGradient → ℝ) : Prop :=
  ∀ (F : PairedGradient) (u v : RegularPotential),
    Integrable (fun q => h (regularTrial F u v q)) domainMeasure ∧
      h F ≤ ∫ q, h (regularTrial F u v q) ∂domainMeasure

def rankOneMinorants (W : PairedGradient → ℝ) : Set (PairedGradient → ℝ) :=
  {h | RankOneConvex h ∧ ∀ F, h F ≤ W F}

def quasiconvexMinorants (W : PairedGradient → ℝ) : Set (PairedGradient → ℝ) :=
  {h | PeriodicQuasiconvex h ∧ ∀ F, h F ≤ W F}

/-- Pointwise supremum of all rank-one convex minorants. -/
def rankOneEnvelope (W : PairedGradient → ℝ) (F : PairedGradient) : ℝ :=
  sSup ((fun h => h F) '' rankOneMinorants W)

/-- Pointwise supremum of all periodic quasiconvex minorants. -/
def quasiconvexEnvelope (W : PairedGradient → ℝ) (F : PairedGradient) : ℝ :=
  sSup ((fun h => h F) '' quasiconvexMinorants W)

theorem rankOne_values_bddAbove (W : PairedGradient → ℝ) (F : PairedGradient) :
    BddAbove ((fun h => h F) '' rankOneMinorants W) := by
  refine ⟨W F, ?_⟩
  rintro y ⟨h, hh, rfl⟩
  exact hh.2 F

theorem quasiconvex_values_bddAbove (W : PairedGradient → ℝ) (F : PairedGradient) :
    BddAbove ((fun h => h F) '' quasiconvexMinorants W) := by
  refine ⟨W F, ?_⟩
  rintro y ⟨h, hh, rfl⟩
  exact hh.2 F

theorem le_rankOneEnvelope {W h : PairedGradient → ℝ}
    (hc : RankOneConvex h) (hb : ∀ F, h F ≤ W F) (F : PairedGradient) :
    h F ≤ rankOneEnvelope W F :=
  le_csSup (rankOne_values_bddAbove W F) ⟨h, ⟨hc,hb⟩, rfl⟩

theorem zero_periodicQuasiconvex : PeriodicQuasiconvex (fun _ => 0) := by
  intro F u v
  exact ⟨integrable_zero _ _ _, by simp⟩

theorem zero_rankOneConvex : RankOneConvex (fun _ => 0) := by
  intro F₁ F₂ h a
  simp

theorem quasiconvex_values_nonempty {W : PairedGradient → ℝ}
    (hW : ∀ F, 0 ≤ W F) (F : PairedGradient) :
    ((fun h => h F) '' quasiconvexMinorants W).Nonempty :=
  ⟨0, ⟨fun _ => 0, ⟨zero_periodicQuasiconvex,hW⟩, rfl⟩⟩

theorem quasiconvexEnvelope_le {W : PairedGradient → ℝ}
    (hW : ∀ F, 0 ≤ W F) (F : PairedGradient) (a : ℝ)
    (ha : ∀ h ∈ quasiconvexMinorants W, h F ≤ a) :
    quasiconvexEnvelope W F ≤ a := by
  apply csSup_le (quasiconvex_values_nonempty hW F)
  rintro y ⟨h,hh,rfl⟩
  exact ha h hh

theorem rankOneEnvelope_le {W : PairedGradient → ℝ}
    (hW : ∀ F, 0 ≤ W F) (F : PairedGradient) : rankOneEnvelope W F ≤ W F := by
  apply csSup_le
    (show ((fun h => h F) '' rankOneMinorants W).Nonempty from
      ⟨0, ⟨fun _ => 0, ⟨zero_rankOneConvex,hW⟩,rfl⟩⟩)
  rintro y ⟨h,hh,rfl⟩
  exact hh.2 F

end HierarchicalLaminates.TwoWell
