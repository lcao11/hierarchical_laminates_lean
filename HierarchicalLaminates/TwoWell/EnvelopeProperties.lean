module

public import HierarchicalLaminates.TwoWell.Envelopes

/-! For a nonnegative obstacle, the rank-one envelope is its greatest rank-one convex minorant. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.TwoWell

open HierarchicalLaminates.Lamination

theorem rankOne_values_nonempty {W : PairedGradient → ℝ}
    (hW : ∀ F, 0 ≤ W F) (F : PairedGradient) :
    ((fun h => h F) '' rankOneMinorants W).Nonempty :=
  ⟨0,⟨fun _ => 0,⟨zero_rankOneConvex,hW⟩,rfl⟩⟩

theorem rankOneEnvelope_nonneg {W : PairedGradient → ℝ}
    (hW : ∀ F, 0 ≤ W F) (F : PairedGradient) : 0 ≤ rankOneEnvelope W F :=
  le_rankOneEnvelope zero_rankOneConvex hW F

theorem rankOneEnvelope_rankOneConvex {W : PairedGradient → ℝ}
    (hW : ∀ F, 0 ≤ W F) : RankOneConvex (rankOneEnvelope W) := by
  intro F₁ F₂ hcompat a
  apply csSup_le (rankOne_values_nonempty hW _)
  rintro y ⟨h,hh,rfl⟩
  have h₁ := le_rankOneEnvelope hh.1 hh.2 F₁
  have h₂ := le_rankOneEnvelope hh.1 hh.2 F₂
  calc
    h ((a : ℝ) • F₁+(1-(a : ℝ)) • F₂) ≤
      (a : ℝ)*h F₁+(1-(a : ℝ))*h F₂ := hh.1 F₁ F₂ hcompat a
    _ ≤ (a : ℝ)*rankOneEnvelope W F₁+(1-(a : ℝ))*rankOneEnvelope W F₂ :=
      add_le_add (mul_le_mul_of_nonneg_left h₁ a.property.1)
        (mul_le_mul_of_nonneg_left h₂ (sub_nonneg.mpr a.property.2))

theorem rankOneEnvelope_isGreatest {W : PairedGradient → ℝ}
    (hW : ∀ F, 0 ≤ W F) :
    IsGreatest (rankOneMinorants W) (rankOneEnvelope W) := by
  refine ⟨⟨rankOneEnvelope_rankOneConvex hW,rankOneEnvelope_le hW⟩,?_⟩
  intro h hh F
  exact le_rankOneEnvelope hh.1 hh.2 F

theorem quasiconvexEnvelope_nonneg {W : PairedGradient → ℝ}
    (hW : ∀ F, 0 ≤ W F) (F : PairedGradient) : 0 ≤ quasiconvexEnvelope W F :=
  le_csSup (quasiconvex_values_bddAbove W F)
    ⟨fun _ => 0,⟨zero_periodicQuasiconvex,hW⟩,rfl⟩

theorem quasiconvexEnvelope_le_energy {W : PairedGradient → ℝ}
    (hW : ∀ F, 0 ≤ W F) (F : PairedGradient) : quasiconvexEnvelope W F ≤ W F := by
  apply quasiconvexEnvelope_le hW F (W F)
  intro h hh
  exact hh.2 F

end HierarchicalLaminates.TwoWell
