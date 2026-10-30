module

public import HierarchicalLaminates.TwoWell.IntegralContinuity
public import HierarchicalLaminates.TwoWell.PeriodicTrials
public import HierarchicalLaminates.TwoWell.SobolevEnvelopes
public import HierarchicalLaminates.TwoWell.WellProperties

/-! The quasiconvex trial inequality for every weak H¹ potential.

The envelope is the supremum of periodic C¹ Jensen minorants. Density of
regular gradients and strong-L² continuity of the nonlinear energy integral
extend its trial bound to every periodic weak H¹ potential.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.TwoWell

open MeasureTheory HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Composition

theorem twoWellIntegral_shift_continuous (f p : PhysicalField) :
    Continuous (fun z : PhysicalField × PhysicalField =>
      twoWellIntegral (f+z.1,p+z.2)) :=
  twoWellIntegral_continuous.comp
    ((continuous_const.add continuous_fst).prodMk (continuous_const.add continuous_snd))

theorem regularTrial_nonlinear_bound
    (h : PairedGradient → ℝ) (hqc : PeriodicQuasiconvex h)
    (hbelow : ∀ F, h F ≤ twoWellEnergy F) (F : PairedGradient)
    (u v : RegularPotential) :
    h F ≤ twoWellIntegral
      (constantField (WithLp.toLp 2 F.1)+u.field,
        constantField (WithLp.toLp 2 F.2)+v.field) := by
  let e := constantField (WithLp.toLp 2 F.1)+u.field
  let g := constantField (WithLp.toLp 2 F.2)+v.field
  apply (hqc F u v).2.trans
  apply integral_mono_ae (hqc F u v).1 (twoWellEnergy_integrable_fields e g)
  filter_upwards [regularTrial_fields F u v] with q hq
  rw [hq]
  exact hbelow _

/-- The universal minorant comparison extends to every closed weak gradient. -/
theorem closedTrial_nonlinear_bound
    (h : PairedGradient → ℝ) (hqc : PeriodicQuasiconvex h)
    (hbelow : ∀ F, h F ≤ twoWellEnergy F) (F : PairedGradient)
    (g₁ g₂ : PhysicalField) (hg₁ : g₁ ∈ gradientSpace) (hg₂ : g₂ ∈ gradientSpace) :
    h F ≤ twoWellIntegral
      (constantField (WithLp.toLp 2 F.1)+g₁,
        constantField (WithLp.toLp 2 F.2)+g₂) := by
  exact regularPair_comparison
    (fun z => twoWellIntegral (constantField (WithLp.toLp 2 F.1)+z.1,
      constantField (WithLp.toLp 2 F.2)+z.2))
    (twoWellIntegral_shift_continuous _ _) (h F)
    (regularTrial_nonlinear_bound h hqc hbelow F) g₁ g₂ hg₁ hg₂

theorem weakTrial_fields (F : PairedGradient) (u v : SobolevPotential) :
    (fun q => (((constantField (WithLp.toLp 2 F.1)+u.gradient) q : Gradient16),
      ((constantField (WithLp.toLp 2 F.2)+v.gradient) q : Gradient16))) =ᵐ[domainMeasure]
      weakTrial F u v := by
  filter_upwards [Lp.coeFn_add (constantField (WithLp.toLp 2 F.1)) u.gradient,
    Lp.coeFn_add (constantField (WithLp.toLp 2 F.2)) v.gradient,
    Lp.coeFn_const 2 domainMeasure (WithLp.toLp 2 F.1),
    Lp.coeFn_const 2 domainMeasure (WithLp.toLp 2 F.2)] with q he hg hf hp
  change constantField (WithLp.toLp 2 F.1) q = WithLp.toLp 2 F.1 at hf
  change constantField (WithLp.toLp 2 F.2) q = WithLp.toLp 2 F.2 at hp
  rw [he,hg]
  simp only [Pi.add_apply]
  rw [hf,hp]
  rfl

theorem weakTrial_twoWell_integrable (F : PairedGradient) (u v : SobolevPotential) :
    Integrable (fun q => twoWellEnergy (weakTrial F u v q)) domainMeasure := by
  apply (twoWellEnergy_integrable_fields
    (constantField (WithLp.toLp 2 F.1)+u.gradient)
    (constantField (WithLp.toLp 2 F.2)+v.gradient)).congr
  exact (weakTrial_fields F u v).mono (fun q hq => congrArg twoWellEnergy hq)

theorem weakTrial_twoWellIntegral (F : PairedGradient) (u v : SobolevPotential) :
    twoWellIntegral (constantField (WithLp.toLp 2 F.1)+u.gradient,
      constantField (WithLp.toLp 2 F.2)+v.gradient) =
      ∫ q, twoWellEnergy (weakTrial F u v q) ∂domainMeasure :=
  integral_congr_ae ((weakTrial_fields F u v).mono
    (fun _q hq => congrArg twoWellEnergy hq))

theorem quasiconvex_minorant_h1_trial_inequality
    (h : PairedGradient → ℝ) (hqc : PeriodicQuasiconvex h)
    (hbelow : ∀ F, h F ≤ twoWellEnergy F)
    (F : PairedGradient) (u v : SobolevPotential) :
    h F ≤ ∫ q, twoWellEnergy (weakTrial F u v q) ∂domainMeasure := by
  have hb := closedTrial_nonlinear_bound h hqc hbelow F u.gradient v.gradient
    (weakGradient_mem_gradientSpace u) (weakGradient_mem_gradientSpace v)
  rwa [weakTrial_twoWellIntegral] at hb

/-- The periodic C¹ Jensen envelope satisfies the weak-H¹ trial inequality. -/
theorem quasiconvex_h1_trial_inequality (F : PairedGradient) (u v : SobolevPotential) :
    quasiconvexEnvelope twoWellEnergy F ≤
      ∫ q, twoWellEnergy (weakTrial F u v q) ∂domainMeasure := by
  apply quasiconvexEnvelope_le twoWellEnergy_nonneg
  intro h hh
  exact quasiconvex_minorant_h1_trial_inequality h hh.1 hh.2 F u v

end HierarchicalLaminates.TwoWell
