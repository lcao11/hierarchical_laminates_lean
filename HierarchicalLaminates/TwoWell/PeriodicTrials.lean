module

public import HierarchicalLaminates.TwoWell.Envelopes
public import HierarchicalLaminates.TwoWell.PeriodicEnergy

/-! The quasiconvex upper bound through periodic C¹ trial potentials.

The cell solver's gradient corrections lie in the closed weak-gradient space.
Density of C¹ gradients and continuity of the selected-phase quadratic integral
extend the periodic Jensen bound to the cell fields.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.TwoWell

open MeasureTheory Matrix HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.WeakCalculus
  HierarchicalLaminates.Analysis HierarchicalLaminates.Material HierarchicalLaminates.Lamination HierarchicalLaminates.Composition

theorem twoWellEnergy_le_selected (b : PhaseFraction)
    (hb : ∀ q, b.value q = 0 ∨ b.value q = 1) (q : Domain) (F : PairedGradient) :
    twoWellEnergy F ≤ pairedEnergy (mixtureTensor (b.value q)) F := by
  rcases hb q with h | h
  · simp [h,mixtureTensor_zero,twoWellEnergy,wellZero]
  · simp [h,mixtureTensor_one,twoWellEnergy,wellOne]

theorem regularTrial_fields (F : PairedGradient) (u v : RegularPotential) :
    (fun q => (((constantField (WithLp.toLp 2 F.1) + u.field) q : Gradient16),
      ((constantField (WithLp.toLp 2 F.2) + v.field) q : Gradient16))) =ᵐ[domainMeasure]
      regularTrial F u v := by
  filter_upwards [Lp.coeFn_add (constantField (WithLp.toLp 2 F.1)) u.field,
    Lp.coeFn_add (constantField (WithLp.toLp 2 F.2)) v.field,
    Lp.coeFn_const 2 domainMeasure (WithLp.toLp 2 F.1),
    Lp.coeFn_const 2 domainMeasure (WithLp.toLp 2 F.2),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure u.gradient,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure v.gradient]
    with q he hg hf hp hu hv
  change constantField (WithLp.toLp 2 F.1) q = WithLp.toLp 2 F.1 at hf
  change constantField (WithLp.toLp 2 F.2) q = WithLp.toLp 2 F.2 at hp
  change u.field q = u.gradient q at hu
  change v.field q = v.gradient q at hv
  rw [he,hg]
  simp only [Pi.add_apply]
  rw [hf,hp,hu,hv]
  rfl

theorem regularTrial_minorant_bound (b : PhaseFraction)
    (hb : ∀ q, b.value q = 0 ∨ b.value q = 1)
    (h : PairedGradient → ℝ) (hqc : PeriodicQuasiconvex h)
    (hbelow : ∀ F, h F ≤ twoWellEnergy F) (F : PairedGradient)
    (u v : RegularPotential) :
    h F ≤ selectedPairEnergy b
      (constantField (WithLp.toLp 2 F.1) + u.field)
      (constantField (WithLp.toLp 2 F.2) + v.field) := by
  let e := constantField (WithLp.toLp 2 F.1) + u.field
  let g := constantField (WithLp.toLp 2 F.2) + v.field
  have hp := regularTrial_fields F u v
  have hi := selectedPairEnergy_integrable b hb e g
  rw [selectedPairEnergy_eq_integral b hb]
  apply (hqc F u v).2.trans
  apply integral_mono_ae (hqc F u v).1 hi
  filter_upwards [hp] with q hq
  exact (hbelow (regularTrial F u v q)).trans
    (hq ▸ twoWellEnergy_le_selected b hb q ((e q : Gradient16),(g q : Gradient16)))

/-- Density extends the periodic C¹ trial bound to closed weak gradients. -/
theorem regularPair_comparison (E : PhysicalField × PhysicalField → ℝ)
    (hE : Continuous E) (a : ℝ)
    (hr : ∀ u v : RegularPotential, a ≤ E (u.field,v.field))
    (g₁ g₂ : PhysicalField) (hg₁ : g₁ ∈ gradientSpace) (hg₂ : g₂ ∈ gradientSpace) :
    a ≤ E (g₁,g₂) := by
  have hc : IsClosed {z : PhysicalField × PhysicalField | a ≤ E z} :=
    isClosed_le continuous_const hE
  have hs : (regularGradients : Set PhysicalField) ×ˢ
      (regularGradients : Set PhysicalField) ⊆ {z | a ≤ E z} := by
    rintro ⟨x,y⟩ ⟨⟨u,rfl⟩,⟨v,rfl⟩⟩
    exact hr u v
  have hm : (g₁,g₂) ∈ closure ((regularGradients : Set PhysicalField) ×ˢ
      (regularGradients : Set PhysicalField)) := by
    rw [closure_prod_eq]
    change g₁ ∈ regularGradients.topologicalClosure ∧
      g₂ ∈ regularGradients.topologicalClosure
    rw [regularGradients_closure_eq]
    exact ⟨hg₁,hg₂⟩
  exact closure_minimal hs hc hm

theorem closedTrial_minorant_bound (b : PhaseFraction)
    (hb : ∀ q, b.value q = 0 ∨ b.value q = 1)
    (h : PairedGradient → ℝ) (hqc : PeriodicQuasiconvex h)
    (hbelow : ∀ F, h F ≤ twoWellEnergy F) (F : PairedGradient)
    (g₁ g₂ : PhysicalField) (hg₁ : g₁ ∈ gradientSpace) (hg₂ : g₂ ∈ gradientSpace) :
    h F ≤ selectedPairEnergy b
      (constantField (WithLp.toLp 2 F.1)+g₁)
      (constantField (WithLp.toLp 2 F.2)+g₂) := by
  let E : PhysicalField × PhysicalField → ℝ := fun z => selectedPairEnergy b
    (constantField (WithLp.toLp 2 F.1)+z.1)
    (constantField (WithLp.toLp 2 F.2)+z.2)
  have hE : Continuous E := selectedPairEnergy_shift_continuous b _ _
  exact regularPair_comparison E hE (h F)
    (regularTrial_minorant_bound b hb h hqc hbelow F) g₁ g₂ hg₁ hg₂

/-- Every periodic quasiconvex minorant satisfies the effective-energy upper bound. -/
theorem periodic_minorant_upper (b : PhaseFraction)
    (hb : ∀ q, b.value q = 0 ∨ b.value q = 1)
    (h : PairedGradient → ℝ) (hqc : PeriodicQuasiconvex h)
    (hbelow : ∀ F, h F ≤ twoWellEnergy F) (f η : PhysicalGradient) :
    h ((f : Gradient16),rotate (effectiveMatrix b *ᵥ (η : Gradient16))) ≤
      quadraticEnergy (effectiveMatrix b) (f : Gradient16) +
        quadraticEnergy (effectiveMatrix b) (η : Gradient16) := by
  let p := HierarchicalLaminates.Material.effectiveOperator b η
  let F : PairedGradient := ((f : Gradient16),(rotatePhysical p : Gradient16))
  have hbound := closedTrial_minorant_bound b hb h hqc hbelow F
    (exactCellField b f-constantField f)
    (rotateField (coefficientLaw b (exactCellField b η))-constantField (rotatePhysical p))
    (exactCellField_isCell b f).1 (exactCellFlux_rotation_admissible b η)
  have h1 : WithLp.toLp 2 F.1 = f := rfl
  have h2 : WithLp.toLp 2 F.2 = rotatePhysical p := rfl
  rw [h1,h2,add_sub_cancel,add_sub_cancel] at hbound
  rw [selectedPairEnergy_exact_fields b hb] at hbound
  have hp : (p : Gradient16) = effectiveMatrix b *ᵥ (η : Gradient16) := by
    dsimp [p]
    rw [←effectiveMatrix_operator]
    rfl
  simpa only [F,rotatePhysical_apply,hp] using hbound

end HierarchicalLaminates.TwoWell
