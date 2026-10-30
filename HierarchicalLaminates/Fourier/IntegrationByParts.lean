module

public import HierarchicalLaminates.Fourier.Differentiation
public import HierarchicalLaminates.Fourier.Mean
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Integration by parts for periodic coordinate derivatives

Haar translation preserves the integral. Differentiation gives zero mean
for each continuous periodic derivative, and the product rule gives the
weak-gradient identity against every smooth test.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Fourier

open MeasureTheory
open scoped Topology

theorem coordinateFlow_zero (i : Fin 2) (q : PeriodicDomain) :
    HierarchicalLaminates.Periodic.coordinateFlow i q 0 = q := by
  simp [HierarchicalLaminates.Periodic.coordinateFlow]

theorem coordinateFlow_add (i : Fin 2) (q : PeriodicDomain) (s t : ℝ) :
    HierarchicalLaminates.Periodic.coordinateFlow i (HierarchicalLaminates.Periodic.coordinateFlow i q s) t =
      HierarchicalLaminates.Periodic.coordinateFlow i q (s + t) := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [HierarchicalLaminates.Periodic.coordinateFlow, add_assoc]
  · simp [HierarchicalLaminates.Periodic.coordinateFlow, Pi.single_eq_of_ne hji]

theorem smoothTest_hasDerivAt_flow (test : HierarchicalLaminates.Periodic.SmoothTest)
    (i : Fin 2) (q : PeriodicDomain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => test.value (HierarchicalLaminates.Periodic.coordinateFlow i q s))
      (test.derivative i (HierarchicalLaminates.Periodic.coordinateFlow i q t)) t := by
  have h0 : HasDerivAt
      (fun s : ℝ => test.value (HierarchicalLaminates.Periodic.coordinateFlow i
        (HierarchicalLaminates.Periodic.coordinateFlow i q t) s))
      (test.derivative i (HierarchicalLaminates.Periodic.coordinateFlow i q t)) (t - t) := by
    simpa only [sub_self] using test.hasPartial i (HierarchicalLaminates.Periodic.coordinateFlow i q t)
  have h := h0.comp t (h := fun s : ℝ => s - t) ((hasDerivAt_id t).sub_const t)
  convert h using 1
  · ext s
    simp only [Function.comp_apply]
    rw [coordinateFlow_add]
    have heq : t + (s - t) = s := by ring
    rw [heq]
  · simp

local instance : Measure.IsAddRightInvariant HierarchicalLaminates.Periodic.domainMeasure := by
  dsimp [HierarchicalLaminates.Periodic.domainMeasure]
  infer_instance

theorem coordinateFlow_integral (f : C(PeriodicDomain, ℝ)) (i : Fin 2) (s : ℝ) :
    (∫ q, f (HierarchicalLaminates.Periodic.coordinateFlow i q s)
      ∂HierarchicalLaminates.Periodic.domainMeasure) =
      ∫ q, f q ∂HierarchicalLaminates.Periodic.domainMeasure :=
  integral_add_right_eq_self f (Pi.single i (s : UnitAddCircle))

theorem periodic_continuous_integrable (f : C(PeriodicDomain, ℝ)) :
    Integrable f HierarchicalLaminates.Periodic.domainMeasure :=
  memLp_one_iff_integrable.mp (ContinuousMap.memLp HierarchicalLaminates.Periodic.domainMeasure ℝ f)

theorem integral_coordinateDerivative_zero (f d : C(PeriodicDomain, ℝ)) (i : Fin 2)
    (hd : ∀ q t, HasDerivAt
      (fun s : ℝ => f (HierarchicalLaminates.Periodic.coordinateFlow i q s))
      (d (HierarchicalLaminates.Periodic.coordinateFlow i q t)) t) :
    (∫ q, d q ∂HierarchicalLaminates.Periodic.domainMeasure) = 0 := by
  let F : ℝ → PeriodicDomain → ℝ := fun s q =>
    f (HierarchicalLaminates.Periodic.coordinateFlow i q s)
  let F' : ℝ → PeriodicDomain → ℝ := fun s q =>
    d (HierarchicalLaminates.Periodic.coordinateFlow i q s)
  have hcont (h : C(PeriodicDomain, ℝ)) (s : ℝ) :
      Continuous (fun q => h (HierarchicalLaminates.Periodic.coordinateFlow i q s)) :=
    h.continuous.comp (continuous_id.add continuous_const)
  have hdiff := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (μ := HierarchicalLaminates.Periodic.domainMeasure)
    (bound := fun _ => ‖d‖) (s := Set.univ) (x₀ := (0 : ℝ))
    Filter.univ_mem
    (Filter.Eventually.of_forall (fun s => (hcont f s).aestronglyMeasurable))
    (by simpa only [F, coordinateFlow_zero] using periodic_continuous_integrable f)
    ((hcont d 0).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun q s _ => d.norm_coe_le_norm _))
    (integrable_const _)
    (Filter.Eventually.of_forall (fun q t _ => hd q t))
  have heq : (fun s : ℝ => ∫ q, F s q ∂HierarchicalLaminates.Periodic.domainMeasure) =
      fun _ : ℝ => ∫ q, f q ∂HierarchicalLaminates.Periodic.domainMeasure := by
    funext s
    exact coordinateFlow_integral f i s
  have hz := hdiff.2
  rw [heq] at hz
  simpa only [F', coordinateFlow_zero] using
    hz.unique (hasDerivAt_const (0 : ℝ) (∫ q, f q ∂HierarchicalLaminates.Periodic.domainMeasure))

theorem integral_coordinateDerivative_mul
    (f d : C(PeriodicDomain, ℝ)) (i : Fin 2)
    (hd : ∀ q t, HasDerivAt
      (fun s : ℝ => f (HierarchicalLaminates.Periodic.coordinateFlow i q s))
      (d (HierarchicalLaminates.Periodic.coordinateFlow i q t)) t)
    (test : HierarchicalLaminates.Periodic.SmoothTest) :
    (∫ q, d q * test.value q ∂HierarchicalLaminates.Periodic.domainMeasure) =
      -(∫ q, f q * test.derivative i q ∂HierarchicalLaminates.Periodic.domainMeasure) := by
  have hprod := integral_coordinateDerivative_zero (f * test.value)
    (d * test.value + f * test.derivative i) i (fun q t =>
      (hd q t).mul (smoothTest_hasDerivAt_flow test i q t))
  change (∫ q, d q * test.value q + f q * test.derivative i q
    ∂HierarchicalLaminates.Periodic.domainMeasure) = 0 at hprod
  have h₁ : Integrable (fun q => d q * test.value q) HierarchicalLaminates.Periodic.domainMeasure := by
    exact (periodic_continuous_integrable (d * test.value)).congr
      (Filter.Eventually.of_forall (fun q => ContinuousMap.mul_apply _ _ q))
  have h₂ : Integrable (fun q => f q * test.derivative i q) HierarchicalLaminates.Periodic.domainMeasure := by
    exact (periodic_continuous_integrable (f * test.derivative i)).congr
      (Filter.Eventually.of_forall (fun q => ContinuousMap.mul_apply _ _ q))
  rw [integral_add h₁ h₂] at hprod
  exact eq_neg_of_add_eq_zero_left hprod

theorem continuousField_inner (f g : C(PeriodicDomain, ℝ)) :
    inner ℝ (HierarchicalLaminates.Periodic.continuousField f)
      (HierarchicalLaminates.Periodic.continuousField g) =
      ∫ q, f q * g q ∂HierarchicalLaminates.Periodic.domainMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) HierarchicalLaminates.Periodic.domainMeasure f,
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) HierarchicalLaminates.Periodic.domainMeasure g]
      with q hf hg
  change inner ℝ (ContinuousMap.toLp 2 HierarchicalLaminates.Periodic.domainMeasure ℝ f q)
    (ContinuousMap.toLp 2 HierarchicalLaminates.Periodic.domainMeasure ℝ g q) = _
  rw [hf, hg]
  simp only [Real.inner_apply]

def gradientComponent (G : C(PeriodicDomain, HierarchicalLaminates.Periodic.PhysicalGradient))
    (i : Fin 2) (a : Fin 16) : C(PeriodicDomain, ℝ) :=
  ⟨fun q => G q (i, a),
    (EuclideanSpace.proj (𝕜 := ℝ) (i, a)).continuous.comp G.continuous⟩

theorem componentField_continuousField
    (G : C(PeriodicDomain, HierarchicalLaminates.Periodic.PhysicalGradient))
    (i : Fin 2) (a : Fin 16) :
    HierarchicalLaminates.Periodic.componentField i a (HierarchicalLaminates.Periodic.continuousField G) =
      HierarchicalLaminates.Periodic.continuousField (gradientComponent G i a) := by
  apply Lp.ext
  filter_upwards
    [(EuclideanSpace.proj (𝕜 := ℝ) (i, a)).coeFn_compLpL
      (HierarchicalLaminates.Periodic.continuousField G),
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) HierarchicalLaminates.Periodic.domainMeasure G,
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) HierarchicalLaminates.Periodic.domainMeasure
        (gradientComponent G i a)] with q hcomp hG hgrad
  change (EuclideanSpace.proj (𝕜 := ℝ) (i, a)).compLpL 2
    HierarchicalLaminates.Periodic.domainMeasure (HierarchicalLaminates.Periodic.continuousField G) q = _
  rw [hcomp]
  change (EuclideanSpace.proj (𝕜 := ℝ) (i, a))
    (ContinuousMap.toLp 2 HierarchicalLaminates.Periodic.domainMeasure ℝ G q) =
      ContinuousMap.toLp 2 HierarchicalLaminates.Periodic.domainMeasure ℝ (gradientComponent G i a) q
  rw [hG, hgrad]
  rfl

theorem continuous_hasWeakGradient
    (u : Fin 16 → C(PeriodicDomain, ℝ))
    (G : C(PeriodicDomain, HierarchicalLaminates.Periodic.PhysicalGradient))
    (hG : ∀ i a q t, HasDerivAt
      (fun s : ℝ => u a (HierarchicalLaminates.Periodic.coordinateFlow i q s))
      (G (HierarchicalLaminates.Periodic.coordinateFlow i q t) (i, a)) t) :
    HierarchicalLaminates.Periodic.HasWeakGradient
      (fun a => HierarchicalLaminates.Periodic.continuousField (u a))
      (HierarchicalLaminates.Periodic.continuousField G) := by
  intro i a test
  rw [componentField_continuousField, continuousField_inner, continuousField_inner]
  exact integral_coordinateDerivative_mul (u a) (gradientComponent G i a) i (hG i a) test

theorem continuous_gradient_mem
    (u : Fin 16 → C(PeriodicDomain, ℝ))
    (G : C(PeriodicDomain, HierarchicalLaminates.Periodic.PhysicalGradient))
    (hG : ∀ i a q t, HasDerivAt
      (fun s : ℝ => u a (HierarchicalLaminates.Periodic.coordinateFlow i q s))
      (G (HierarchicalLaminates.Periodic.coordinateFlow i q t) (i, a)) t) :
    HierarchicalLaminates.Periodic.continuousField G ∈ HierarchicalLaminates.Periodic.gradientSpace := by
  apply HierarchicalLaminates.Periodic.weakGradientSpace.le_topologicalClosure
  exact ⟨fun a => HierarchicalLaminates.Periodic.continuousField (u a),
    continuous_hasWeakGradient u G hG⟩

end HierarchicalLaminates.Fourier
