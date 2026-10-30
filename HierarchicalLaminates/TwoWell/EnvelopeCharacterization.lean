module

public import HierarchicalLaminates.TwoWell.EnvelopeProperties
public import HierarchicalLaminates.TwoWell.WellProperties
public import HierarchicalLaminates.TwoWell.QuasiconvexRankOne
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Greatest periodic quasiconvex minorants

The admissible functions are real-valued periodic Jensen minorants. For a
nonnegative obstacle, taking the maximum with zero gives a cofinal nonnegative
subclass with the same pointwise supremum.

The rank-one implication uses only a continuous upper obstacle. The
greatest-minorant theorem additionally requires a nonnegative obstacle; it
proves measurability and trial integrability of the supremum before applying
the Jensen inequality to that supremum.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.TwoWell

open MeasureTheory HierarchicalLaminates HierarchicalLaminates.Periodic
  HierarchicalLaminates.Composition

theorem PeriodicQuasiconvex.max {h k : PairedGradient → ℝ}
    (hh : PeriodicQuasiconvex h) (hk : PeriodicQuasiconvex k) :
    PeriodicQuasiconvex (fun F => max (h F) (k F)) := by
  intro F u v
  have hi := (hh F u v).1.sup (hk F u v).1
  refine ⟨hi, max_le ?_ ?_⟩
  · exact (hh F u v).2.trans
      (integral_mono (hh F u v).1 hi (fun _ => le_max_left _ _))
  · exact (hk F u v).2.trans
      (integral_mono (hk F u v).1 hi (fun _ => le_max_right _ _))

theorem PeriodicQuasiconvex.add_const {h : PairedGradient → ℝ}
    (hh : PeriodicQuasiconvex h) (c : ℝ) :
    PeriodicQuasiconvex (fun F => h F+c) := by
  intro F u v
  refine ⟨(hh F u v).1.add (integrable_const c),?_⟩
  calc
    h F+c ≤ (∫ q, h (regularTrial F u v q) ∂domainMeasure)+c :=
      by linarith [(hh F u v).2]
    _ = ∫ q, h (regularTrial F u v q)+c ∂domainMeasure := by
      rw [integral_add (hh F u v).1 (integrable_const c)]
      simp

theorem constant_periodicQuasiconvex (c : ℝ) : PeriodicQuasiconvex (fun _ => c) := by
  simpa only [zero_add] using zero_periodicQuasiconvex.add_const c

def nonnegativeTruncation (h : PairedGradient → ℝ) (c : ℝ) (F : PairedGradient) : ℝ :=
  max (h F) c-c

theorem PeriodicQuasiconvex.nonnegativeTruncation {h : PairedGradient → ℝ}
    (hh : PeriodicQuasiconvex h) (c : ℝ) :
    PeriodicQuasiconvex (nonnegativeTruncation h c) := by
  change PeriodicQuasiconvex (fun F => Max.max (h F) c-c)
  simpa only [sub_eq_add_neg] using
    (hh.max (constant_periodicQuasiconvex c)).add_const (-c)

theorem nonnegativeTruncation_nonneg (h : PairedGradient → ℝ) (c : ℝ) (F : PairedGradient) :
    0 ≤ nonnegativeTruncation h c F :=
  sub_nonneg.mpr (le_max_right _ _)

theorem nonnegativeTruncation_le {h W : PairedGradient → ℝ}
    (hle : ∀ F, h F ≤ W F) (c : ℝ) (F : PairedGradient) :
    nonnegativeTruncation h c F ≤ nonnegativeTruncation W c F :=
  sub_le_sub_right (max_le_max (hle F) le_rfl) c

theorem nonnegativeTruncation_continuous {W : PairedGradient → ℝ}
    (hW : Continuous W) (c : ℝ) : Continuous (nonnegativeTruncation W c) :=
  (hW.max continuous_const).sub continuous_const

/-- Every real-valued periodic minorant of a continuous obstacle is
rank-one convex. Truncation at the endpoint values reduces the proof to the
nonnegative case. -/
theorem PeriodicQuasiconvex.rankOneConvex_of_le_continuous
    {h W : PairedGradient → ℝ} (hh : PeriodicQuasiconvex h)
    (hW : Continuous W) (hle : ∀ F, h F ≤ W F) : RankOneConvex h := by
  intro F₁ F₂ hcompat a
  let c := min (h F₁) (h F₂)
  let g : PairedGradient → ℝ := fun F => Max.max (h F) c-c
  let U : PairedGradient → ℝ := fun F => Max.max (W F) c-c
  have hg : PeriodicQuasiconvex g := hh.nonnegativeTruncation c
  have hU : Continuous U := (hW.max continuous_const).sub continuous_const
  have hgb : ∀ F, g F ≤ U F := fun F =>
    sub_le_sub_right (max_le_max (hle F) le_rfl) c
  have hgrc : RankOneConvex g := hg.rankOneConvex_of_nonneg_le
    (fun _ => sub_nonneg.mpr (le_max_right _ _)) hU hgb
  have hi := hgrc F₁ F₂ hcompat a
  have h₁ : g F₁ = h F₁-c := by
    change Max.max (h F₁) c-c = h F₁-c
    rw [max_eq_left (min_le_left (h F₁) (h F₂))]
  have h₂ : g F₂ = h F₂-c := by
    change Max.max (h F₂) c-c = h F₂-c
    rw [max_eq_left (min_le_right (h F₁) (h F₂))]
  have hm : h ((a : ℝ) • F₁+(1-(a : ℝ)) • F₂)-c ≤
      g ((a : ℝ) • F₁+(1-(a : ℝ)) • F₂) :=
    sub_le_sub_right (le_max_left _ _) c
  rw [h₁,h₂] at hi
  nlinarith

theorem twoWell_periodicQuasiconvex_rankOneConvex {h : PairedGradient → ℝ}
    (hh : PeriodicQuasiconvex h) (hle : ∀ F, h F ≤ twoWellEnergy F) : RankOneConvex h :=
  hh.rankOneConvex_of_le_continuous twoWellEnergy_continuous hle

theorem quasiconvexMinorants_max_zero {W h : PairedGradient → ℝ}
    (hW : ∀ F, 0 ≤ W F) (hh : h ∈ quasiconvexMinorants W) :
    (fun F => max (h F) 0) ∈ quasiconvexMinorants W := by
  exact ⟨hh.1.max zero_periodicQuasiconvex, fun F => max_le (hh.2 F) (hW F)⟩

def nonnegativeQuasiconvexMinorants (W : PairedGradient → ℝ) :
    Set (PairedGradient → ℝ) :=
  {h | h ∈ quasiconvexMinorants W ∧ ∀ F, 0 ≤ h F}

theorem nonnegativeQuasiconvexMinorants_cofinal {W : PairedGradient → ℝ}
    (hW : ∀ F, 0 ≤ W F) {h : PairedGradient → ℝ}
    (hh : h ∈ quasiconvexMinorants W) :
    ∃ k ∈ nonnegativeQuasiconvexMinorants W, h ≤ k := by
  refine ⟨fun F => max (h F) 0, ?_, fun F => le_max_left _ _⟩
  exact ⟨quasiconvexMinorants_max_zero hW hh, fun F => le_max_right _ _⟩

theorem nonnegativeQuasiconvex_values_nonempty {W : PairedGradient → ℝ}
    (hW : ∀ F, 0 ≤ W F) (F : PairedGradient) :
    ((fun h => h F) '' nonnegativeQuasiconvexMinorants W).Nonempty := by
  exact ⟨0, fun _ => 0, ⟨⟨zero_periodicQuasiconvex,hW⟩, fun _ => le_rfl⟩, rfl⟩

theorem nonnegativeQuasiconvex_values_bddAbove (W : PairedGradient → ℝ)
    (F : PairedGradient) :
    BddAbove ((fun h => h F) '' nonnegativeQuasiconvexMinorants W) := by
  refine ⟨W F, ?_⟩
  rintro r ⟨h, hh, rfl⟩
  exact hh.1.2 F

theorem quasiconvexEnvelope_eq_nonnegative_sup {W : PairedGradient → ℝ}
    (hW : ∀ F, 0 ≤ W F) (F : PairedGradient) :
    quasiconvexEnvelope W F =
      sSup ((fun h => h F) '' nonnegativeQuasiconvexMinorants W) := by
  apply le_antisymm
  · apply quasiconvexEnvelope_le hW F
    intro h hh
    obtain ⟨k, hk, hle⟩ := nonnegativeQuasiconvexMinorants_cofinal hW hh
    exact (hle F).trans (le_csSup (nonnegativeQuasiconvex_values_bddAbove W F)
      ⟨k,hk,rfl⟩)
  · apply csSup_le (nonnegativeQuasiconvex_values_nonempty hW F)
    rintro r ⟨h, hh, rfl⟩
    exact le_csSup (quasiconvex_values_bddAbove W F) ⟨h,hh.1,rfl⟩

theorem quasiconvexEnvelope_eq_nonnegative_iSup {W : PairedGradient → ℝ}
    (hW : ∀ F, 0 ≤ W F) (F : PairedGradient) :
    quasiconvexEnvelope W F =
      ⨆ h : {h // h ∈ nonnegativeQuasiconvexMinorants W}, h.1 F := by
  rw [quasiconvexEnvelope_eq_nonnegative_sup hW]
  change sSup _ = sSup _
  congr 1
  ext r
  constructor
  · rintro ⟨h,hh,rfl⟩
    exact ⟨⟨h,hh⟩,rfl⟩
  · rintro ⟨⟨h,hh⟩,rfl⟩
    exact ⟨h,hh,rfl⟩

theorem quasiconvexEnvelope_lowerSemicontinuous_of_minorants
    {W : PairedGradient → ℝ} (hW : ∀ F, 0 ≤ W F)
    (hc : ∀ h ∈ nonnegativeQuasiconvexMinorants W, Continuous h) :
    LowerSemicontinuous (quasiconvexEnvelope W) := by
  have heq : quasiconvexEnvelope W = fun F =>
      ⨆ h : {h // h ∈ nonnegativeQuasiconvexMinorants W}, h.1 F :=
    funext (quasiconvexEnvelope_eq_nonnegative_iSup hW)
  rw [heq]
  apply lowerSemicontinuous_ciSup
  · intro F
    refine ⟨W F, ?_⟩
    rintro r ⟨⟨h,hh⟩,rfl⟩
    exact hh.1.2 F
  · intro h
    exact (hc h.1 h.2).lowerSemicontinuous

theorem le_quasiconvexEnvelope {W h : PairedGradient → ℝ}
    (hh : h ∈ quasiconvexMinorants W) (F : PairedGradient) :
    h F ≤ quasiconvexEnvelope W F :=
  le_csSup (quasiconvex_values_bddAbove W F) ⟨h,hh,rfl⟩

theorem regularTrial_continuous (F : PairedGradient) (u v : RegularPotential) :
    Continuous (regularTrial F u v) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro c
    exact continuous_const.add ((PiLp.continuous_apply 2 (fun _ : Fin 2 × Fin 16 => ℝ) c).comp
      u.gradient.continuous)
  · apply continuous_pi
    intro c
    exact continuous_const.add ((PiLp.continuous_apply 2 (fun _ : Fin 2 × Fin 16 => ℝ) c).comp
      v.gradient.continuous)

theorem continuous_regularTrial_integrable {W : PairedGradient → ℝ}
    (hW : Continuous W) (F : PairedGradient) (u v : RegularPotential) :
    Integrable (fun q => W (regularTrial F u v q)) domainMeasure := by
  let f : C(Domain, ℝ) := ⟨_, hW.comp (regularTrial_continuous F u v)⟩
  exact Integrable.of_bound f.continuous.measurable.aestronglyMeasurable ‖f‖
    (Filter.Eventually.of_forall f.norm_coe_le_norm)

/-- For a continuous nonnegative obstacle, global measurability of the
supremum gives integrability on every regular periodic trial. -/
theorem quasiconvexEnvelope_trial_integrable_of_measurable
    {W : PairedGradient → ℝ} (hW : ∀ F, 0 ≤ W F) (hcont : Continuous W)
    (hmeas : Measurable (quasiconvexEnvelope W))
    (F : PairedGradient) (u v : RegularPotential) :
    Integrable (fun q => quasiconvexEnvelope W (regularTrial F u v q)) domainMeasure := by
  apply (continuous_regularTrial_integrable hcont F u v).mono'
    (hmeas.comp (regularTrial_continuous F u v).measurable).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun q => by
    change ‖quasiconvexEnvelope W (regularTrial F u v q)‖ ≤ W (regularTrial F u v q)
    rw [Real.norm_eq_abs, abs_of_nonneg (quasiconvexEnvelope_nonneg hW _)]
    exact quasiconvexEnvelope_le_energy hW _

/-- Integrability of the envelope's regular trial energies gives its Jensen
inequality by comparison with every admissible minorant. -/
theorem quasiconvexEnvelope_periodicQuasiconvex_of_integrable
    {W : PairedGradient → ℝ} (hW : ∀ F, 0 ≤ W F)
    (hi : ∀ (F : PairedGradient) (u v : RegularPotential),
      Integrable (fun q => quasiconvexEnvelope W (regularTrial F u v q)) domainMeasure) :
    PeriodicQuasiconvex (quasiconvexEnvelope W) := by
  intro F u v
  refine ⟨hi F u v, ?_⟩
  apply quasiconvexEnvelope_le hW F
  intro h hh
  exact (hh.1 F u v).2.trans
    (integral_mono (hh.1 F u v).1 (hi F u v)
      (fun q => le_quasiconvexEnvelope hh (regularTrial F u v q)))

theorem quasiconvexEnvelope_isGreatest_of_integrable
    {W : PairedGradient → ℝ} (hW : ∀ F, 0 ≤ W F)
    (hi : ∀ (F : PairedGradient) (u v : RegularPotential),
      Integrable (fun q => quasiconvexEnvelope W (regularTrial F u v q)) domainMeasure) :
    IsGreatest (quasiconvexMinorants W) (quasiconvexEnvelope W) := by
  refine ⟨⟨quasiconvexEnvelope_periodicQuasiconvex_of_integrable hW hi,
    quasiconvexEnvelope_le_energy hW⟩, ?_⟩
  intro h hh F
  exact le_quasiconvexEnvelope hh F

theorem quasiconvexEnvelope_isGreatest_of_measurable
    {W : PairedGradient → ℝ} (hW : ∀ F, 0 ≤ W F) (hcont : Continuous W)
    (hmeas : Measurable (quasiconvexEnvelope W)) :
    IsGreatest (quasiconvexMinorants W) (quasiconvexEnvelope W) :=
  quasiconvexEnvelope_isGreatest_of_integrable hW
    (quasiconvexEnvelope_trial_integrable_of_measurable hW hcont hmeas)

theorem quasiconvexEnvelope_isGreatest_of_continuous_nonnegative_minorants
    {W : PairedGradient → ℝ} (hW : ∀ F, 0 ≤ W F) (hcont : Continuous W)
    (hc : ∀ h ∈ nonnegativeQuasiconvexMinorants W, Continuous h) :
    IsGreatest (quasiconvexMinorants W) (quasiconvexEnvelope W) :=
  quasiconvexEnvelope_isGreatest_of_measurable hW hcont
    (quasiconvexEnvelope_lowerSemicontinuous_of_minorants hW hc).measurable

/-- The supremum of all admissible periodic minorants is itself the
greatest minorant for every continuous nonnegative obstacle. -/
theorem quasiconvexEnvelope_isGreatest {W : PairedGradient → ℝ}
    (hW : ∀ F, 0 ≤ W F) (hcont : Continuous W) :
    IsGreatest (quasiconvexMinorants W) (quasiconvexEnvelope W) := by
  apply quasiconvexEnvelope_isGreatest_of_continuous_nonnegative_minorants hW hcont
  intro h hh
  exact hh.1.1.continuous_of_nonneg_le hh.2 hcont hh.1.2

theorem quasiconvexEnvelope_periodicQuasiconvex {W : PairedGradient → ℝ}
    (hW : ∀ F, 0 ≤ W F) (hcont : Continuous W) :
    PeriodicQuasiconvex (quasiconvexEnvelope W) :=
  (quasiconvexEnvelope_isGreatest hW hcont).1.1

theorem twoWell_quasiconvexEnvelope_isGreatest :
    IsGreatest (quasiconvexMinorants twoWellEnergy) (quasiconvexEnvelope twoWellEnergy) :=
  quasiconvexEnvelope_isGreatest twoWellEnergy_nonneg twoWellEnergy_continuous

/-- The minorant suprema compare whenever rank-one convexity has
been established for every admissible quasiconvex minorant. -/
theorem quasiconvexEnvelope_le_rankOneEnvelope_of_minorants
    {W : PairedGradient → ℝ} (hW : ∀ F, 0 ≤ W F)
    (hcompat : ∀ h ∈ quasiconvexMinorants W, RankOneConvex h)
    (F : PairedGradient) :
    quasiconvexEnvelope W F ≤ rankOneEnvelope W F := by
  apply quasiconvexEnvelope_le hW F
  intro h hh
  exact le_rankOneEnvelope (hcompat h hh) hh.2 F

theorem quasiconvexEnvelope_le_rankOneEnvelope_of_nonnegative_minorants
    {W : PairedGradient → ℝ} (hW : ∀ F, 0 ≤ W F)
    (hcompat : ∀ h ∈ nonnegativeQuasiconvexMinorants W, RankOneConvex h)
    (F : PairedGradient) :
    quasiconvexEnvelope W F ≤ rankOneEnvelope W F := by
  rw [quasiconvexEnvelope_eq_nonnegative_sup hW]
  apply csSup_le (nonnegativeQuasiconvex_values_nonempty hW F)
  rintro r ⟨h,hh,rfl⟩
  exact le_rankOneEnvelope (hcompat h hh) hh.1.2 F

theorem quasiconvexEnvelope_le_rankOneEnvelope {W : PairedGradient → ℝ}
    (hW : ∀ F, 0 ≤ W F) (hcont : Continuous W) (F : PairedGradient) :
    quasiconvexEnvelope W F ≤ rankOneEnvelope W F := by
  apply quasiconvexEnvelope_le_rankOneEnvelope_of_minorants hW
  intro h hh
  exact hh.1.rankOneConvex_of_le_continuous hcont hh.2

theorem twoWell_quasiconvexEnvelope_le_rankOneEnvelope (F : PairedGradient) :
    quasiconvexEnvelope twoWellEnergy F ≤ rankOneEnvelope twoWellEnergy F :=
  quasiconvexEnvelope_le_rankOneEnvelope twoWellEnergy_nonneg twoWellEnergy_continuous F

end HierarchicalLaminates.TwoWell
