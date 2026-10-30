module

public import HierarchicalLaminates.TwoWell.Envelopes

/-! Comparison of periodic H¹ and C¹ Jensen envelopes.

Every C¹ periodic potential supplies a weak H¹ potential with the same gradient.
Thus every H¹ Jensen minorant is a C¹ Jensen minorant. For a nonnegative
obstacle, the H¹ envelope is bounded above by the C¹ envelope.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.TwoWell

open MeasureTheory HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Composition

/-- A weak H¹ variation in each independent group of sixteen potentials. -/
def weakTrial (F : PairedGradient) (u v : SobolevPotential) (q : Domain) :
    PairedGradient :=
  (F.1 + (fun c => u.gradient q c),F.2 + (fun c => v.gradient q c))

def SobolevQuasiconvex (h : PairedGradient → ℝ) : Prop :=
  ∀ (F : PairedGradient) (u v : SobolevPotential),
    Integrable (fun q => h (weakTrial F u v q)) domainMeasure ∧
      h F ≤ ∫ q, h (weakTrial F u v q) ∂domainMeasure

def regularSobolevPotential (u : RegularPotential) : SobolevPotential where
  potential a := continuousField (u.potential a)
  gradient := u.field
  weakGradient := u.weakGradient

theorem weakTrial_regular (F : PairedGradient) (u v : RegularPotential) :
    weakTrial F (regularSobolevPotential u) (regularSobolevPotential v)
      =ᵐ[domainMeasure] regularTrial F u v := by
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure u.gradient,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure v.gradient] with q hu hv
  change u.field q = u.gradient q at hu
  change v.field q = v.gradient q at hv
  simp only [weakTrial,regularSobolevPotential,regularTrial,hu,hv]

theorem SobolevQuasiconvex.toPeriodicQuasiconvex
    {h : PairedGradient → ℝ} (hh : SobolevQuasiconvex h) : PeriodicQuasiconvex h := by
  intro F u v
  have ht := hh F (regularSobolevPotential u) (regularSobolevPotential v)
  have hae : (fun q => h (weakTrial F (regularSobolevPotential u)
      (regularSobolevPotential v) q)) =ᵐ[domainMeasure]
      fun q => h (regularTrial F u v q) :=
    (weakTrial_regular F u v).mono (fun q hq => congrArg h hq)
  exact ⟨ht.1.congr hae,(integral_congr_ae hae) ▸ ht.2⟩

def sobolevQuasiconvexMinorants (W : PairedGradient → ℝ) :
    Set (PairedGradient → ℝ) :=
  {h | SobolevQuasiconvex h ∧ ∀ F, h F ≤ W F}

def sobolevQuasiconvexEnvelope (W : PairedGradient → ℝ) (F : PairedGradient) : ℝ :=
  sSup ((fun h => h F) '' sobolevQuasiconvexMinorants W)

theorem zero_sobolevQuasiconvex : SobolevQuasiconvex (fun _ => 0) := by
  intro F u v
  exact ⟨integrable_zero _ _ _,by simp⟩

theorem sobolev_values_nonempty {W : PairedGradient → ℝ}
    (hW : ∀ F, 0 ≤ W F) (F : PairedGradient) :
    ((fun h => h F) '' sobolevQuasiconvexMinorants W).Nonempty :=
  ⟨0,⟨fun _ => 0,⟨zero_sobolevQuasiconvex,hW⟩,rfl⟩⟩

theorem sobolev_values_bddAbove (W : PairedGradient → ℝ) (F : PairedGradient) :
    BddAbove ((fun h => h F) '' sobolevQuasiconvexMinorants W) := by
  refine ⟨W F,?_⟩
  rintro y ⟨h,hh,rfl⟩
  exact hh.2 F

/-- For a nonnegative obstacle, the H¹ Jensen envelope is bounded above by
the periodic C¹ Jensen envelope. -/
theorem sobolevEnvelope_le_periodicEnvelope {W : PairedGradient → ℝ}
    (hW : ∀ F, 0 ≤ W F) (F : PairedGradient) :
    sobolevQuasiconvexEnvelope W F ≤ quasiconvexEnvelope W F := by
  apply csSup_le (sobolev_values_nonempty hW F)
  rintro y ⟨h,hh,rfl⟩
  apply le_csSup (quasiconvex_values_bddAbove W F)
  exact ⟨h,⟨hh.1.toPeriodicQuasiconvex,hh.2⟩,rfl⟩

end HierarchicalLaminates.TwoWell
