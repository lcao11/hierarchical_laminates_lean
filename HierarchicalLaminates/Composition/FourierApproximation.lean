module

public import HierarchicalLaminates.Composition.RegularPotential
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Density of regular periodic gradients and rotated gradients
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.Composition

open MeasureTheory HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Fourier
  HierarchicalLaminates.WeakCalculus

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def frequencyAmplitude (k : Frequency) (a : Fin 16) : PhysicalGradient :=
  WithLp.toLp 2 (fun c => if c.2 = a then angularFrequency k c.1 else 0)

@[simp] theorem frequencyAmplitude_apply (k : Frequency) (a b : Fin 16) (i : Fin 2) :
    frequencyAmplitude k a (i, b) = if b = a then angularFrequency k i else 0 := rfl

def cosineGradientPotential (k : Frequency) (a : Fin 16) : RegularPotential where
  potential b := if b = a then sineKernel k else 0
  gradient := cosineKernel k • ContinuousMap.const Domain (frequencyAmplitude k a)
  hasPartial i b q t := by
    by_cases hb : b = a
    · subst b
      convert hasDerivAt_sineKernel_flow_at k i q t using 1 <;>
        simp [frequencyAmplitude, angularFrequency, mul_comm]
    · convert hasDerivAt_const t (0 : ℝ) using 1 <;>
        simp [hb, frequencyAmplitude]

def sineGradientPotential (k : Frequency) (a : Fin 16) : RegularPotential where
  potential b := if b = a then -cosineKernel k else 0
  gradient := sineKernel k • ContinuousMap.const Domain (frequencyAmplitude k a)
  hasPartial i b q t := by
    by_cases hb : b = a
    · subst b
      convert (hasDerivAt_cosineKernel_flow_at k i q t).neg using 1
      · ext s
        simp
      · simp [frequencyAmplitude, angularFrequency, mul_comm]
    · convert hasDerivAt_const t (0 : ℝ) using 1 <;>
        simp [hb, frequencyAmplitude]

def regularGradients : Submodule ℝ PhysicalField where
  carrier := {g | ∃ u : RegularPotential, u.field = g}
  zero_mem' := ⟨RegularPotential.zero, RegularPotential.field_zero⟩
  add_mem' := by
    rintro g h ⟨u, rfl⟩ ⟨v, rfl⟩
    exact ⟨u.add v, RegularPotential.field_add u v⟩
  smul_mem' := by
    rintro c g ⟨u, rfl⟩
    exact ⟨u.smul c, RegularPotential.field_smul c u⟩

def regularCurls : Submodule ℝ PhysicalField := regularGradients.map curlField.toLinearMap

theorem regularGradients_le : regularGradients ≤ gradientSpace := by
  rintro g ⟨u, rfl⟩
  exact u.mem_gradientSpace

theorem regularGradients_closure_le : regularGradients.topologicalClosure ≤ gradientSpace :=
  regularGradients.topologicalClosure_minimal regularGradients_le
    weakGradientSpace.isClosed_topologicalClosure

theorem regularCurls_orthogonal (j : PhysicalField) (hj : j ∈ regularCurls)
    (g : PhysicalField) (hg : g ∈ gradientSpace) : inner ℝ j g = 0 := by
  rcases hj with ⟨_, ⟨u, rfl⟩, rfl⟩
  exact u.curl_orthogonal g hg

theorem regularCurls_mean_zero (j : PhysicalField) (hj : j ∈ regularCurls) :
    meanField j = 0 := by
  rcases hj with ⟨_, ⟨u, rfl⟩, rfl⟩
  exact u.curl_mean_zero

theorem regularCurls_closure_orthogonal (j : PhysicalField)
    (hj : j ∈ regularCurls.topologicalClosure) (g : PhysicalField)
    (hg : g ∈ gradientSpace) : inner ℝ j g = 0 := by
  let L := innerSL ℝ g
  have hsub : regularCurls ≤ L.ker := by
    intro j hj
    change inner ℝ g j = 0
    rw [real_inner_comm]
    exact regularCurls_orthogonal j hj g hg
  have h := regularCurls.topologicalClosure_minimal hsub L.isClosed_ker hj
  change inner ℝ g j = 0 at h
  rwa [real_inner_comm] at h

theorem regularCurls_closure_mean_zero (j : PhysicalField)
    (hj : j ∈ regularCurls.topologicalClosure) : meanField j = 0 := by
  have hsub : regularCurls ≤ (meanField : PhysicalField →L[ℝ] PhysicalGradient).ker := by
    intro j hj
    exact regularCurls_mean_zero j hj
  exact regularCurls.topologicalClosure_minimal hsub meanField.isClosed_ker hj

theorem componentField_mode (φ : C(Domain, ℝ)) (v : PhysicalGradient)
    (i : Fin 2) (a : Fin 16) :
    componentField i a (continuousField (φ • ContinuousMap.const Domain v)) =
      v (i, a) • continuousField φ := by
  apply Lp.ext
  filter_upwards [(EuclideanSpace.proj (𝕜 := ℝ) (i, a)).coeFn_compLpL
      (continuousField (φ • ContinuousMap.const Domain v)),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure
      (φ • ContinuousMap.const Domain v),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure φ,
    Lp.coeFn_smul (v (i, a)) (continuousField φ)] with q hcomp hmode hφ hsmul
  change componentField i a (continuousField (φ • ContinuousMap.const Domain v)) q = _ at hcomp
  change continuousField (φ • ContinuousMap.const Domain v) q = _ at hmode
  change continuousField φ q = _ at hφ
  rw [hcomp, hmode, hsmul]
  change (EuclideanSpace.proj (𝕜 := ℝ) (i, a))
      ((φ • ContinuousMap.const Domain v) q) = v (i, a) * continuousField φ q
  rw [hφ]
  simp [mul_comm]

theorem mode_pairing (φ : C(Domain, ℝ)) (v : PhysicalGradient) (f : PhysicalField) :
    inner ℝ (continuousField (φ • ContinuousMap.const Domain v)) f =
      ∑ a : Fin 16, ∑ i : Fin 2,
        v (i, a) * inner ℝ (componentField i a f) (continuousField φ) := by
  rw [physical_inner_components]
  simp_rw [componentField_mode, real_inner_smul_left,
    real_inner_comm (continuousField φ)]

theorem amplitude_mode_pairing (φ : C(Domain, ℝ)) (k : Frequency) (a : Fin 16)
    (f : PhysicalField) :
    inner ℝ (continuousField (φ • ContinuousMap.const Domain (frequencyAmplitude k a))) f =
      angularFrequency k 0 * inner ℝ (componentField 0 a f) (continuousField φ) +
      angularFrequency k 1 * inner ℝ (componentField 1 a f) (continuousField φ) := by
  rw [mode_pairing]
  simp [Fin.sum_univ_two]

theorem curl_mode (φ : C(Domain, ℝ)) (v : PhysicalGradient) :
    curlField (continuousField (φ • ContinuousMap.const Domain v)) =
      continuousField (φ • ContinuousMap.const Domain (curlOperator v)) := by
  apply Lp.ext
  filter_upwards [curlOperator.coeFn_compLpL
      (continuousField (φ • ContinuousMap.const Domain v)),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure
      (φ • ContinuousMap.const Domain v),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure
      (φ • ContinuousMap.const Domain (curlOperator v))] with q hcurl hmode hout
  change curlField (continuousField (φ • ContinuousMap.const Domain v)) q = _ at hcurl
  change continuousField (φ • ContinuousMap.const Domain v) q = _ at hmode
  change continuousField (φ • ContinuousMap.const Domain (curlOperator v)) q = _ at hout
  rw [hcurl, hmode, hout]
  simp only [ContinuousMap.smul_apply', ContinuousMap.const_apply, map_smul]

theorem curl_amplitude_mode_pairing (φ : C(Domain, ℝ)) (k : Frequency) (a : Fin 16)
    (f : PhysicalField) :
    inner ℝ (curlField
      (continuousField (φ • ContinuousMap.const Domain (frequencyAmplitude k a)))) f =
      -(angularFrequency k 1) * inner ℝ (componentField 0 a f) (continuousField φ) +
      angularFrequency k 0 * inner ℝ (componentField 1 a f) (continuousField φ) := by
  rw [curl_mode, mode_pairing]
  simp only [Fin.sum_univ_two, curlOperator_apply_zero, curlOperator_apply_one,
    frequencyAmplitude_apply]
  simp [Finset.sum_add_distrib, Finset.sum_neg_distrib]

theorem angularFrequency_ne_zero (k : Frequency) (hk : k ≠ (0, 0)) :
    angularFrequency k 0 ≠ 0 ∨ angularFrequency k 1 ≠ 0 := by
  by_contra h
  push Not at h
  have h0 : k.1 = 0 := by
    have hp := Real.pi_pos
    have hz := h.1
    simp only [angularFrequency, frequencyVector, Matrix.cons_val_zero] at hz
    have : (k.1 : ℝ) = 0 := by nlinarith
    exact_mod_cast this
  have h1 : k.2 = 0 := by
    have hp := Real.pi_pos
    have hz := h.2
    change 2 * Real.pi * (k.2 : ℝ) = 0 at hz
    have : (k.2 : ℝ) = 0 := by nlinarith
    exact_mod_cast this
  exact hk (Prod.ext h0 h1)

theorem moment_zero_of_regular_orthogonal (f : PhysicalField)
    (hgrad : ∀ u : RegularPotential, inner ℝ u.field f = 0)
    (hcurl : ∀ u : RegularPotential, inner ℝ (curlField u.field) f = 0)
    (k : Frequency) (hk : k ≠ (0, 0)) (a : Fin 16) :
    (∀ i, inner ℝ (componentField i a f) (continuousField (cosineKernel k)) = 0) ∧
    (∀ i, inner ℝ (componentField i a f) (continuousField (sineKernel k)) = 0) := by
  have hc := hgrad (cosineGradientPotential k a)
  have hcc := hcurl (cosineGradientPotential k a)
  have hs := hgrad (sineGradientPotential k a)
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
  have hpos : 0 < angularFrequency k 0 ^ 2 + angularFrequency k 1 ^ 2 := by
    rcases angularFrequency_ne_zero k hk with h | h
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (angularFrequency k 1)]
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (angularFrequency k 0)]
  have solve (x y : ℝ) (h1 : angularFrequency k 0 * x + angularFrequency k 1 * y = 0)
      (h2 : -(angularFrequency k 1) * x + angularFrequency k 0 * y = 0) :
      x = 0 ∧ y = 0 := by
    have hx : (angularFrequency k 0 ^ 2 + angularFrequency k 1 ^ 2) * x = 0 := by
      linear_combination angularFrequency k 0 * h1 - angularFrequency k 1 * h2
    have hy : (angularFrequency k 0 ^ 2 + angularFrequency k 1 ^ 2) * y = 0 := by
      linear_combination angularFrequency k 1 * h1 + angularFrequency k 0 * h2
    exact ⟨(mul_eq_zero.mp hx).resolve_left hpos.ne',
      (mul_eq_zero.mp hy).resolve_left hpos.ne'⟩
  have hc0 := solve _ _ hc hcc
  have hs0 := solve _ _ hs hsc
  constructor <;> intro i <;> fin_cases i
  · exact hc0.1
  · exact hc0.2
  · exact hs0.1
  · exact hs0.2

theorem scalarField_eq_zero_of_moments (f : ScalarField)
    (hc : ∀ k : Frequency, inner ℝ f (continuousField (cosineKernel k)) = 0)
    (hs : ∀ k : Frequency, inner ℝ f (continuousField (sineKernel k)) = 0) : f = 0 := by
  have hcoeff : ∀ k : Fin 2 → ℤ,
      UnitAddTorus.mFourierCoeff (complexField f) k = 0 := by
    intro k
    have hk : frequencyVector (k 0, k 1) = k := by ext i; fin_cases i <;> rfl
    rw [← hk, coefficient_complexField, hc, hs]
    simp
  have hz : complexField f = 0 := by
    have hsum := UnitAddTorus.hasSum_mFourier_series_L2 (complexField f)
    have hterm (k : Fin 2 → ℤ) : UnitAddTorus.mFourierCoeff (complexField f) k •
        UnitAddTorus.mFourierLp 2 k = 0 := by
      exact (congrArg (fun z : ℂ => z • UnitAddTorus.mFourierLp 2 k) (hcoeff k)).trans
        (zero_smul ℂ _)
    have hzero : HasSum (fun _ : Fin 2 → ℤ => (0 : Lp ℂ 2 domainMeasure))
        (complexField f) := hsum.congr_fun (fun k => (hterm k).symm)
    exact hzero.unique hasSum_zero
  have hin := complexField_inner f f
  rw [hz] at hin
  have hreal : inner ℝ f f = 0 := by
    apply Complex.ofReal_injective
    simpa using hin.symm
  exact inner_self_eq_zero.mp hreal

theorem field_eq_zero_of_regular_orthogonal (f : PhysicalField) (hm : meanField f = 0)
    (hgrad : ∀ u : RegularPotential, inner ℝ u.field f = 0)
    (hcurl : ∀ u : RegularPotential, inner ℝ (curlField u.field) f = 0) : f = 0 := by
  have hc (i : Fin 2) (a : Fin 16) (k : Frequency) :
      inner ℝ (componentField i a f) (continuousField (cosineKernel k)) = 0 := by
    by_cases hk : k = (0, 0)
    · subst k
      rw [cosineKernel_zero]
      have h := constant_mean_pairing (1 : ℝ) (componentField i a f)
      rw [component_mean_eq_coordinate, hm] at h
      have hconst : continuousField (1 : C(Domain, ℝ)) = constantField (1 : ℝ) := by
        exact continuousField_const 1
      rw [hconst, real_inner_comm]
      simpa using h
    · exact (moment_zero_of_regular_orthogonal f hgrad hcurl k hk a).1 i
  have hs (i : Fin 2) (a : Fin 16) (k : Frequency) :
      inner ℝ (componentField i a f) (continuousField (sineKernel k)) = 0 := by
    by_cases hk : k = (0, 0)
    · subst k
      simp [sineKernel_zero]
    · exact (moment_zero_of_regular_orthogonal f hgrad hcurl k hk a).2 i
  have hcomp (i : Fin 2) (a : Fin 16) : componentField i a f = 0 :=
    scalarField_eq_zero_of_moments _ (hc i a) (hs i a)
  have hnorm := physical_inner_components f f
  simp only [hcomp, inner_zero_left, Finset.sum_const_zero] at hnorm
  exact inner_self_eq_zero.mp hnorm

theorem regularGradients_closure_eq : regularGradients.topologicalClosure = gradientSpace := by
  apply le_antisymm regularGradients_closure_le
  intro g hg
  let P := regularGradients.topologicalClosure
  let : CompleteSpace P := regularGradients.isClosed_topologicalClosure.completeSpace_coe
  obtain ⟨v, hv, w, hw, hdecomp⟩ := P.exists_add_mem_mem_orthogonal g
  have hvG : v ∈ gradientSpace := regularGradients_closure_le hv
  have hwG : w ∈ gradientSpace := by
    have heq : w = g - v := by rw [hdecomp]; abel
    rw [heq]
    exact gradientSpace.sub_mem hg hvG
  have hwzero : w = 0 := by
    apply field_eq_zero_of_regular_orthogonal w (gradientSpace_mean_zero w hwG)
    · intro u
      exact hw u.field (regularGradients.le_topologicalClosure ⟨u, rfl⟩)
    · intro u
      exact u.curl_orthogonal w hwG
  rw [hwzero, add_zero] at hdecomp
  exact hdecomp ▸ hv

theorem mem_regularCurls_closure (j : PhysicalField) (hm : meanField j = 0)
    (hj : ∀ g ∈ gradientSpace, inner ℝ j g = 0) :
    j ∈ regularCurls.topologicalClosure := by
  let P := regularCurls.topologicalClosure
  let : CompleteSpace P := regularCurls.isClosed_topologicalClosure.completeSpace_coe
  obtain ⟨v, hv, w, hw, hdecomp⟩ := P.exists_add_mem_mem_orthogonal j
  have hwm : meanField w = 0 := by
    have heq : w = j - v := by rw [hdecomp]; abel
    rw [heq, map_sub, hm, regularCurls_closure_mean_zero v hv, sub_zero]
  have hworth (g : PhysicalField) (hg : g ∈ gradientSpace) : inner ℝ w g = 0 := by
    have heq : w = j - v := by rw [hdecomp]; abel
    rw [heq, inner_sub_left, hj g hg, regularCurls_closure_orthogonal v hv g hg, sub_self]
  have hwzero : w = 0 := by
    apply field_eq_zero_of_regular_orthogonal w hwm
    · intro u
      rw [real_inner_comm]
      exact hworth _ u.mem_gradientSpace
    · intro u
      apply hw
      apply regularCurls.le_topologicalClosure
      exact ⟨u.field, ⟨u, rfl⟩, rfl⟩
  rw [hwzero, add_zero] at hdecomp
  exact hdecomp ▸ hv

/-- Every field in the closed weak-gradient space is approximated by regular periodic gradients. -/
theorem exists_regular_gradient_approx (g : PhysicalField) (hg : g ∈ gradientSpace)
    (ε : ℝ) (hε : 0 < ε) : ∃ u : RegularPotential, ‖u.field - g‖ < ε := by
  have hmem : g ∈ closure (regularGradients : Set PhysicalField) := by
    change g ∈ regularGradients.topologicalClosure
    rw [regularGradients_closure_eq]
    exact hg
  obtain ⟨y, ⟨u, hu⟩, hdist⟩ := Metric.mem_closure_iff.mp hmem ε hε
  refine ⟨u, ?_⟩
  rw [hu]
  simpa only [dist_eq_norm, norm_sub_rev] using hdist

/-- Approximate every mean-zero equilibrated field by a rotated regular gradient. -/
theorem exists_regular_curl_approx (j : PhysicalField) (hm : meanField j = 0)
    (hj : ∀ g ∈ gradientSpace, inner ℝ j g = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ u : RegularPotential, ‖curlField u.field - j‖ < ε := by
  have hmem : j ∈ closure (regularCurls : Set PhysicalField) :=
    mem_regularCurls_closure j hm hj
  obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.mp hmem ε hε
  rcases hy with ⟨_, ⟨u, rfl⟩, rfl⟩
  refine ⟨u, ?_⟩
  change dist j (curlField u.field) < ε at hdist
  rw [dist_eq_norm, norm_sub_rev] at hdist
  exact hdist

end HierarchicalLaminates.Composition
