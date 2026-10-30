module

public import HierarchicalLaminates.Corrector.Smoothness
public import HierarchicalLaminates.TwoWell.Envelopes32
public import HierarchicalLaminates.TwoWell.PeriodicWitness
public import HierarchicalLaminates.TwoWell.IntegralContinuity
public import HierarchicalLaminates.TwoWell.WellProperties

/-!
# Smooth and C¹ periodic Jensen tests under explicit energy continuity

Jointly `C∞` periodic potential gradients are dense in the weak-gradient space.
For a continuous integrand `h` whose field-energy integral is continuous in the
strong `L²` topology, Jensen tests with these smooth potentials are equivalent
to all C¹ periodic tests. Integrability of each C¹ test energy follows from
continuity on its compact range.

The two-well energy satisfies the required continuity hypotheses. Smooth
potentials also give energies below every strict upper margin above the
selected pair of quadratic cell energies.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.TwoWell

open Matrix MeasureTheory Set Filter Periodic Fourier WeakCalculus HierarchicalLaminates.Composition
open scoped ContDiff

/-- A regular potential whose real periodic lifts are jointly C∞. -/
def SmoothPotential := {u : RegularPotential // ∀ a,ContDiff ℝ ∞ (realLift (u.potential a))}

def SmoothPotential.zero : SmoothPotential := ⟨RegularPotential.zero,fun _ => contDiff_const⟩

def SmoothPotential.add (u v : SmoothPotential) : SmoothPotential :=
  ⟨u.1.add v.1,fun a => (u.2 a).add (v.2 a)⟩

def SmoothPotential.smul (c : ℝ) (u : SmoothPotential) : SmoothPotential :=
  ⟨u.1.smul c,fun a => (u.2 a).const_smul c⟩

def smoothCosineGradientPotential (k : Frequency) (a : Fin 16) : SmoothPotential := by
  refine ⟨cosineGradientPotential k a,?_⟩
  intro b
  by_cases hb : b = a
  · subst b
    have he : (cosineGradientPotential k a).potential a = sineKernel k := by simp [cosineGradientPotential]
    rw [he]
    change ContDiff ℝ ∞ (torusLift (sineKernel k))
    rw [sineKernel_lift]
    fun_prop
  · change ContDiff ℝ ∞ (realLift (if b = a then sineKernel k else 0))
    rw [ite_eq_right hb]
    exact contDiff_const

def smoothSineGradientPotential (k : Frequency) (a : Fin 16) : SmoothPotential := by
  refine ⟨sineGradientPotential k a,?_⟩
  intro b
  by_cases hb : b = a
  · subst b
    have he : (sineGradientPotential k a).potential a = -cosineKernel k := by simp [sineGradientPotential]
    rw [he]
    have hs : ContDiff ℝ ∞ (torusLift (cosineKernel k)) := by
      rw [cosineKernel_lift]
      fun_prop
    have heq : realLift (-cosineKernel k) = fun x => -torusLift (cosineKernel k) x := by
      funext x
      exact ContinuousMap.neg_apply (cosineKernel k) (fun i => (x i : UnitAddCircle))
    rw [heq]
    exact hs.neg
  · change ContDiff ℝ ∞ (realLift (if b = a then -cosineKernel k else 0))
    rw [ite_eq_right hb]
    exact contDiff_const

def smoothGradients : Submodule ℝ PhysicalField where
  carrier := {g | ∃ u : SmoothPotential,u.1.field = g}
  zero_mem' := ⟨SmoothPotential.zero,RegularPotential.field_zero⟩
  add_mem' := by
    rintro g h ⟨u,rfl⟩ ⟨v,rfl⟩
    exact ⟨u.add v,RegularPotential.field_add u.1 v.1⟩
  smul_mem' := by
    rintro c g ⟨u,rfl⟩
    exact ⟨u.smul c,RegularPotential.field_smul c u.1⟩

theorem smoothGradients_closure_le : smoothGradients.topologicalClosure ≤ gradientSpace := by
  apply smoothGradients.topologicalClosure_minimal _ weakGradientSpace.isClosed_topologicalClosure
  rintro g ⟨u,rfl⟩
  exact u.1.mem_gradientSpace

private theorem moment_zero_of_smooth_orthogonal (f : PhysicalField)
    (hgrad : ∀ u : SmoothPotential,inner ℝ u.1.field f = 0)
    (hcurl : ∀ u : RegularPotential,inner ℝ (curlField u.field) f = 0)
    (k : Frequency) (hk : k ≠ (0,0)) (a : Fin 16) :
    (∀ i,inner ℝ (componentField i a f) (continuousField (cosineKernel k)) = 0) ∧
      (∀ i,inner ℝ (componentField i a f) (continuousField (sineKernel k)) = 0) := by
  have hc := hgrad (smoothCosineGradientPotential k a)
  have hs := hgrad (smoothSineGradientPotential k a)
  have hcc := hcurl (cosineGradientPotential k a)
  have hsc := hcurl (sineGradientPotential k a)
  change inner ℝ (continuousField
    (cosineKernel k • ContinuousMap.const Domain (frequencyAmplitude k a))) f = 0 at hc
  change inner ℝ (continuousField
    (sineKernel k • ContinuousMap.const Domain (frequencyAmplitude k a))) f = 0 at hs
  change inner ℝ (curlField (continuousField
    (cosineKernel k • ContinuousMap.const Domain (frequencyAmplitude k a)))) f = 0 at hcc
  change inner ℝ (curlField (continuousField
    (sineKernel k • ContinuousMap.const Domain (frequencyAmplitude k a)))) f = 0 at hsc
  rw [amplitude_mode_pairing] at hc hs
  rw [curl_amplitude_mode_pairing] at hcc hsc
  have hp : 0 < angularFrequency k 0^2+angularFrequency k 1^2 := by
    rcases angularFrequency_ne_zero k hk with h | h
    · nlinarith [sq_pos_of_ne_zero h,sq_nonneg (angularFrequency k 1)]
    · nlinarith [sq_pos_of_ne_zero h,sq_nonneg (angularFrequency k 0)]
  have solve (x y : ℝ) (h1 : angularFrequency k 0*x+angularFrequency k 1*y = 0)
      (h2 : -(angularFrequency k 1)*x+angularFrequency k 0*y = 0) : x = 0 ∧ y = 0 := by
    have hx : (angularFrequency k 0^2+angularFrequency k 1^2)*x = 0 := by
      linear_combination angularFrequency k 0*h1-angularFrequency k 1*h2
    have hy : (angularFrequency k 0^2+angularFrequency k 1^2)*y = 0 := by
      linear_combination angularFrequency k 1*h1+angularFrequency k 0*h2
    exact ⟨(mul_eq_zero.mp hx).resolve_left hp.ne',(mul_eq_zero.mp hy).resolve_left hp.ne'⟩
  have hc0 := solve _ _ hc hcc
  have hs0 := solve _ _ hs hsc
  constructor <;> intro i <;> fin_cases i
  · exact hc0.1
  · exact hc0.2
  · exact hs0.1
  · exact hs0.2

private theorem field_eq_zero_of_smooth_orthogonal (f : PhysicalField)
    (hm : meanField f = 0)
    (hgrad : ∀ u : SmoothPotential,inner ℝ u.1.field f = 0)
    (hcurl : ∀ u : RegularPotential,inner ℝ (curlField u.field) f = 0) : f = 0 := by
  have hc (i : Fin 2) (a : Fin 16) (k : Frequency) :
      inner ℝ (componentField i a f) (continuousField (cosineKernel k)) = 0 := by
    by_cases hk : k = (0,0)
    · subst k
      rw [cosineKernel_zero]
      have h := constant_mean_pairing (1 : ℝ) (componentField i a f)
      rw [component_mean_eq_coordinate,hm] at h
      have hconst : continuousField (1 : C(Domain,ℝ)) = constantField (1 : ℝ) := continuousField_const 1
      rw [hconst,real_inner_comm]
      simpa using h
    · exact (moment_zero_of_smooth_orthogonal f hgrad hcurl k hk a).1 i
  have hs (i : Fin 2) (a : Fin 16) (k : Frequency) :
      inner ℝ (componentField i a f) (continuousField (sineKernel k)) = 0 := by
    by_cases hk : k = (0,0)
    · subst k
      simp [sineKernel_zero]
    · exact (moment_zero_of_smooth_orthogonal f hgrad hcurl k hk a).2 i
  have hcomp (i : Fin 2) (a : Fin 16) : componentField i a f = 0 :=
    scalarField_eq_zero_of_moments _ (hc i a) (hs i a)
  have hn := physical_inner_components f f
  simp only [hcomp,inner_zero_left,Finset.sum_const_zero] at hn
  exact inner_self_eq_zero.mp hn

/-- Jointly smooth periodic gradients are dense in the full weak-gradient space. -/
theorem smoothGradients_closure_eq : smoothGradients.topologicalClosure = gradientSpace := by
  apply le_antisymm smoothGradients_closure_le
  intro g hg
  let P := smoothGradients.topologicalClosure
  let : CompleteSpace P := smoothGradients.isClosed_topologicalClosure.completeSpace_coe
  obtain ⟨v,hv,w,hw,hd⟩ := P.exists_add_mem_mem_orthogonal g
  have hvG : v ∈ gradientSpace := smoothGradients_closure_le hv
  have hwG : w ∈ gradientSpace := by
    have heq : w = g-v := by rw [hd]; abel
    rw [heq]
    exact gradientSpace.sub_mem hg hvG
  have hwzero : w = 0 := by
    apply field_eq_zero_of_smooth_orthogonal w (gradientSpace_mean_zero w hwG)
    · intro u
      exact hw u.1.field (smoothGradients.le_topologicalClosure ⟨u,rfl⟩)
    · intro u
      exact u.curl_orthogonal w hwG
  rw [hwzero,add_zero] at hd
  exact hd ▸ hv

def SmoothPeriodicQuasiconvex (h : PairedGradient → ℝ) : Prop :=
  ∀ (F : PairedGradient) (u v : SmoothPotential),
    Integrable (fun q => h (regularTrial F u.1 v.1 q)) domainMeasure ∧
      h F ≤ ∫ q,h (regularTrial F u.1 v.1 q) ∂domainMeasure

/-- The nonlinear integral of `h` evaluated on two `L²` fields. -/
def fieldEnergyIntegral (h : PairedGradient → ℝ) (z : PhysicalField × PhysicalField) : ℝ :=
  ∫ q,h ((z.1 q : Gradient16),(z.2 q : Gradient16)) ∂domainMeasure

theorem smoothPair_comparison (E : PhysicalField × PhysicalField → ℝ)
    (hE : Continuous E) (a : ℝ)
    (hs : ∀ u v : SmoothPotential,a ≤ E (u.1.field,v.1.field))
    (g₁ g₂ : PhysicalField) (hg₁ : g₁ ∈ gradientSpace) (hg₂ : g₂ ∈ gradientSpace) :
    a ≤ E (g₁,g₂) := by
  have hc : IsClosed {z : PhysicalField × PhysicalField | a ≤ E z} := isClosed_le continuous_const hE
  have hs' : (smoothGradients : Set PhysicalField) ×ˢ (smoothGradients : Set PhysicalField) ⊆
      {z : PhysicalField × PhysicalField | a ≤ E z} := by
    rintro ⟨x,y⟩ ⟨⟨u,rfl⟩,⟨v,rfl⟩⟩
    exact hs u v
  have hm : (g₁,g₂) ∈ closure ((smoothGradients : Set PhysicalField) ×ˢ
      (smoothGradients : Set PhysicalField)) := by
    rw [closure_prod_eq]
    change g₁ ∈ smoothGradients.topologicalClosure ∧ g₂ ∈ smoothGradients.topologicalClosure
    rw [smoothGradients_closure_eq]
    exact ⟨hg₁,hg₂⟩
  exact closure_minimal hs' hc hm

theorem regularTrial_integral_eq_fieldEnergy (h : PairedGradient → ℝ) (F : PairedGradient)
    (u v : RegularPotential) :
    (∫ q,h (regularTrial F u v q) ∂domainMeasure) =
      fieldEnergyIntegral h (constantField (WithLp.toLp 2 F.1)+u.field,
        constantField (WithLp.toLp 2 F.2)+v.field) :=
  (integral_congr_ae ((regularTrial_fields F u v).mono (fun _ hq => congrArg h hq))).symm

theorem continuous_regularTrial_energy_integrable {h : PairedGradient → ℝ} (hc : Continuous h)
    (F : PairedGradient) (u v : RegularPotential) :
    Integrable (fun q => h (regularTrial F u v q)) domainMeasure := by
  have htrial : Continuous (regularTrial F u v) := by
    apply Continuous.prodMk
    · apply continuous_pi
      intro c
      exact continuous_const.add ((PiLp.continuous_apply 2 (fun _ : Fin 2 × Fin 16 => ℝ) c).comp
        u.gradient.continuous)
    · apply continuous_pi
      intro c
      exact continuous_const.add ((PiLp.continuous_apply 2 (fun _ : Fin 2 × Fin 16 => ℝ) c).comp
        v.gradient.continuous)
  let f : C(Domain,ℝ) := ⟨_,hc.comp htrial⟩
  exact Integrable.of_bound f.continuous.measurable.aestronglyMeasurable ‖f‖
    (Filter.Eventually.of_forall f.norm_coe_le_norm)

/-- Smooth and C¹ Jensen tests agree when `h` is continuous and its field-energy
integral is continuous in the strong `L²` topology. -/
theorem smoothPeriodicQuasiconvex_iff {h : PairedGradient → ℝ} (hc : Continuous h)
    (hE : Continuous (fieldEnergyIntegral h)) :
    SmoothPeriodicQuasiconvex h ↔ PeriodicQuasiconvex h := by
  constructor
  · intro hh F u v
    refine ⟨continuous_regularTrial_energy_integrable hc F u v,?_⟩
    rw [regularTrial_integral_eq_fieldEnergy]
    apply smoothPair_comparison
      (fun z => fieldEnergyIntegral h (constantField (WithLp.toLp 2 F.1)+z.1,
        constantField (WithLp.toLp 2 F.2)+z.2))
      (hE.comp ((continuous_const.add continuous_fst).prodMk (continuous_const.add continuous_snd)))
      (h F) ?_ u.field v.field u.mem_gradientSpace v.mem_gradientSpace
    intro us vs
    rw [← regularTrial_integral_eq_fieldEnergy]
    exact (hh F us vs).2
  · intro hh F u v
    exact hh F u.1 v.1

theorem twoWell_smoothPeriodicQuasiconvex_iff :
    SmoothPeriodicQuasiconvex twoWellEnergy ↔ PeriodicQuasiconvex twoWellEnergy :=
  smoothPeriodicQuasiconvex_iff twoWellEnergy_continuous twoWellIntegral_continuous

theorem twoWell_fieldEnergy_integrable (z : PhysicalField × PhysicalField) :
    Integrable (fun q => twoWellEnergy ((z.1 q : Gradient16),(z.2 q : Gradient16))) domainMeasure :=
  twoWellEnergy_integrable_fields z.1 z.2

theorem twoWell_fieldEnergyIntegral_continuous : Continuous (fieldEnergyIntegral twoWellEnergy) :=
  twoWellIntegral_continuous

def SmoothPeriodicQuasiconvex32 (h : Gradient32 → ℝ) : Prop :=
  ∀ (F : Gradient32) (u v : SmoothPotential),
    Integrable (fun q => h (regularTrial32 F u.1 v.1 q)) domainMeasure ∧
      h F ≤ ∫ q,h (regularTrial32 F u.1 v.1 q) ∂domainMeasure

theorem smoothQuasiconvex32_pullback (h : Gradient32 → ℝ) :
    SmoothPeriodicQuasiconvex32 h ↔ SmoothPeriodicQuasiconvex (fun F => h (join32 F)) := by
  constructor
  · intro hh F u v
    simpa only [regularTrial32,split32_join32] using hh (join32 F) u v
  · intro hh F u v
    simpa only [regularTrial32,join32_split32] using hh (split32 F) u v

theorem twoWell32_smoothPeriodicQuasiconvex_iff :
    SmoothPeriodicQuasiconvex32 twoWellEnergy32 ↔ PeriodicQuasiconvex32 twoWellEnergy32 := by
  rw [smoothQuasiconvex32_pullback,quasiconvex32_pullback]
  simpa only [twoWellEnergy32_join32] using twoWell_smoothPeriodicQuasiconvex_iff

theorem exists_smoothPair_lt (E : PhysicalField × PhysicalField → ℝ) (hE : Continuous E)
    (a : ℝ) (g₁ g₂ : PhysicalField) (hg₁ : g₁ ∈ gradientSpace) (hg₂ : g₂ ∈ gradientSpace)
    (ha : E (g₁,g₂) < a) : ∃ u v : SmoothPotential,E (u.1.field,v.1.field) < a := by
  by_contra hn
  push Not at hn
  exact (not_lt_of_ge (smoothPair_comparison E hE a hn g₁ g₂ hg₁ hg₂)) ha

/-- Jointly `C∞` periodic potentials have two-well energy below every strict
upper margin above the sum of the two selected physical cell energies. -/
theorem exists_smooth_trial_lt (b : Material.PhaseFraction)
    (hb : ∀ q,b.value q = 0 ∨ b.value q = 1) (f η : PhysicalGradient)
    (a : ℝ) (ha : Lamination.quadraticEnergy (Material.effectiveMatrix b) (f : Gradient16)+
      Lamination.quadraticEnergy (Material.effectiveMatrix b) (η : Gradient16) < a) :
    ∃ u v : SmoothPotential,
      (∫ q,twoWellEnergy (regularTrial
        ((f : Gradient16),rotate (Material.effectiveMatrix b *ᵥ (η : Gradient16))) u.1 v.1 q)
          ∂domainMeasure) < a := by
  let p := Material.effectiveOperator b η
  let F : PairedGradient := ((f : Gradient16),(rotatePhysical p : Gradient16))
  let g₁ := exactCellField b f-constantField f
  let g₂ := rotateField (Material.coefficientLaw b (exactCellField b η))-constantField (rotatePhysical p)
  let E : PhysicalField × PhysicalField → ℝ := fun z =>
    selectedPairEnergy b (constantField f+z.1) (constantField (rotatePhysical p)+z.2)
  have he : E (g₁,g₂) = Lamination.quadraticEnergy (Material.effectiveMatrix b) (f : Gradient16)+
      Lamination.quadraticEnergy (Material.effectiveMatrix b) (η : Gradient16) := by
    dsimp [E,g₁,g₂]
    rw [add_sub_cancel,add_sub_cancel,selectedPairEnergy_exact_fields b hb]
  obtain ⟨u,v,huv⟩ := exists_smoothPair_lt E (selectedPairEnergy_shift_continuous b _ _) a g₁ g₂
    (exactCellField_isCell b f).1 (exactCellFlux_rotation_admissible b η) (he ▸ ha)
  have ht := (regularTrial_energy_le_selected b hb F u.1 v.1).trans_lt huv
  have hp : (p : Gradient16) = Material.effectiveMatrix b *ᵥ (η : Gradient16) := by
    dsimp [p]
    rw [← Material.effectiveMatrix_operator]
    rfl
  exact ⟨u,v,by simpa only [F,rotatePhysical_apply,hp] using ht⟩

theorem exists_smooth_trial32_lt (b : Material.PhaseFraction)
    (hb : ∀ q,b.value q = 0 ∨ b.value q = 1) (f η : PhysicalGradient)
    (a : ℝ) (ha : Lamination.quadraticEnergy (Material.effectiveMatrix b) (f : Gradient16)+
      Lamination.quadraticEnergy (Material.effectiveMatrix b) (η : Gradient16) < a) :
    ∃ u v : SmoothPotential,
      (∫ q,twoWellEnergy32 (regularTrial32
        (join32 ((f : Gradient16),rotate (Material.effectiveMatrix b *ᵥ (η : Gradient16))))
          u.1 v.1 q) ∂domainMeasure) < a := by
  obtain ⟨u,v,huv⟩ := exists_smooth_trial_lt b hb f η a ha
  exact ⟨u,v,by simpa only [regularTrial32,split32_join32,twoWellEnergy32_join32] using huv⟩

end HierarchicalLaminates.TwoWell
