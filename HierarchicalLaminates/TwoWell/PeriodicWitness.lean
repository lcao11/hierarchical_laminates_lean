module

public import HierarchicalLaminates.TwoWell.PeriodicTrials

/-! Regular periodic variations realizing every strict upper-energy margin. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.TwoWell

open MeasureTheory Matrix HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.WeakCalculus
  HierarchicalLaminates.Analysis HierarchicalLaminates.Material HierarchicalLaminates.Lamination HierarchicalLaminates.Composition

theorem exists_regularPair_lt (E : PhysicalField × PhysicalField → ℝ)
    (hE : Continuous E) (a : ℝ) (g₁ g₂ : PhysicalField)
    (hg₁ : g₁ ∈ gradientSpace) (hg₂ : g₂ ∈ gradientSpace)
    (ha : E (g₁,g₂) < a) :
    ∃ u v : RegularPotential, E (u.field,v.field) < a := by
  by_contra hn
  push Not at hn
  exact (not_lt_of_ge (regularPair_comparison E hE a hn g₁ g₂ hg₁ hg₂)) ha

theorem regularTrial_twoWell_integrable (F : PairedGradient) (u v : RegularPotential) :
    Integrable (fun q => twoWellEnergy (regularTrial F u v q)) domainMeasure := by
  apply (twoWellEnergy_integrable_fields
    (constantField (WithLp.toLp 2 F.1)+u.field)
    (constantField (WithLp.toLp 2 F.2)+v.field)).congr
  filter_upwards [regularTrial_fields F u v] with q hq
  exact congrArg twoWellEnergy hq

theorem regularTrial_energy_le_selected (b : PhaseFraction)
    (hb : ∀ q, b.value q = 0 ∨ b.value q = 1)
    (F : PairedGradient) (u v : RegularPotential) :
    (∫ q, twoWellEnergy (regularTrial F u v q) ∂domainMeasure) ≤
      selectedPairEnergy b
        (constantField (WithLp.toLp 2 F.1)+u.field)
        (constantField (WithLp.toLp 2 F.2)+v.field) := by
  let e := constantField (WithLp.toLp 2 F.1)+u.field
  let g := constantField (WithLp.toLp 2 F.2)+v.field
  rw [selectedPairEnergy_eq_integral b hb]
  apply integral_mono_ae (regularTrial_twoWell_integrable F u v)
    (selectedPairEnergy_integrable b hb e g)
  filter_upwards [regularTrial_fields F u v] with q hq
  rw [←hq]
  exact twoWellEnergy_le_selected b hb q _

/-- Periodic C¹ potentials approach the selected effective-energy bound. -/
theorem exists_regular_trial_lt (b : PhaseFraction)
    (hb : ∀ q, b.value q = 0 ∨ b.value q = 1) (f η : PhysicalGradient)
    (a : ℝ) (ha : quadraticEnergy (effectiveMatrix b) (f : Gradient16) +
      quadraticEnergy (effectiveMatrix b) (η : Gradient16) < a) :
    ∃ u v : RegularPotential,
      (∫ q, twoWellEnergy (regularTrial
        ((f : Gradient16),rotate (effectiveMatrix b *ᵥ (η : Gradient16))) u v q) ∂domainMeasure) < a := by
  let p := HierarchicalLaminates.Material.effectiveOperator b η
  let F : PairedGradient := ((f : Gradient16),(rotatePhysical p : Gradient16))
  let g₁ := exactCellField b f-constantField f
  let g₂ := rotateField (coefficientLaw b (exactCellField b η))-
    constantField (rotatePhysical p)
  let E : PhysicalField × PhysicalField → ℝ := fun z =>
    selectedPairEnergy b (constantField f+z.1) (constantField (rotatePhysical p)+z.2)
  have hE : Continuous E := selectedPairEnergy_shift_continuous b _ _
  have he : E (g₁,g₂) = quadraticEnergy (effectiveMatrix b) (f : Gradient16) +
      quadraticEnergy (effectiveMatrix b) (η : Gradient16) := by
    dsimp [E,g₁,g₂]
    rw [add_sub_cancel,add_sub_cancel,selectedPairEnergy_exact_fields b hb]
  obtain ⟨u,v,huv⟩ := exists_regularPair_lt E hE a g₁ g₂
    (exactCellField_isCell b f).1 (exactCellFlux_rotation_admissible b η) (he ▸ ha)
  have htrial := regularTrial_energy_le_selected b hb F u v
  have ht : (∫ q, twoWellEnergy (regularTrial F u v q) ∂domainMeasure) < a :=
    htrial.trans_lt huv
  have hp : (p : Gradient16) = effectiveMatrix b *ᵥ (η : Gradient16) := by
    dsimp [p]
    rw [←effectiveMatrix_operator]
    rfl
  refine ⟨u,v,?_⟩
  simpa only [F,rotatePhysical_apply,hp] using ht

end HierarchicalLaminates.TwoWell
