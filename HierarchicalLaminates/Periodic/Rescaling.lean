module

public import HierarchicalLaminates.Periodic.WeakGradient
public import HierarchicalLaminates.Periodic.CellEnergy
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Coordinate rescaling of the normalized periodic cell

For `L > 0`, multiplying coordinates by `L` maps the unit torus to the period-L
torus. This map transports normalized Haar measure and induces L² isometries
preserving integrals. Pulling a potential back as `v(Lq) / L` preserves its
gradient under the same coordinate change, so every macroscopic loading has
the same weak Sobolev cell energy at both periods.

The normalized torus integral equals the open-square Lebesgue average, since
the boundary of the periodic cell has measure zero.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Periodic

open MeasureTheory
open scoped Topology ContDiff

abbrev PeriodDomain (L : ℝ) := Fin 2 → AddCircle L

variable (L : ℝ) [hL : Fact (0 < L)]

def periodMeasure : Measure (PeriodDomain L) :=
  Measure.pi (fun _ : Fin 2 => AddCircle.haarAddCircle (T := L))

instance periodMeasure_probability : IsProbabilityMeasure (periodMeasure L) := by
  dsimp [periodMeasure]
  infer_instance

def scaleCircle : UnitAddCircle ≃+ AddCircle L :=
  AddCircle.equivAddCircle 1 L (by norm_num) hL.out.ne'

def scaleTorus : Domain ≃ₜ PeriodDomain L :=
  Homeomorph.piCongrRight (fun _ : Fin 2 =>
    AddCircle.homeomorphAddCircle 1 L (by norm_num) hL.out.ne')

theorem scaleTorus_apply (q : Domain) (i : Fin 2) :
    scaleTorus L q i = scaleCircle L (q i) := rfl

theorem scaleTorus_symm_apply (q : PeriodDomain L) (i : Fin 2) :
    (scaleTorus L).symm q i = (scaleCircle L).symm (q i) := rfl

theorem scaleTorus_coe (x : Fin 2 → ℝ) :
    scaleTorus L (fun i => (x i : UnitAddCircle)) = fun i => (L * x i : AddCircle L) := by
  ext i
  simp [scaleTorus_apply, scaleCircle, mul_comm]

theorem scaleTorus_symm_coe (x : Fin 2 → ℝ) :
    (scaleTorus L).symm (fun i => (x i : AddCircle L)) =
      fun i => (x i / L : UnitAddCircle) := by
  ext i
  simp [scaleTorus_symm_apply, scaleCircle, div_eq_mul_inv]

theorem scaleCircle_measurePreserving :
    MeasurePreserving (scaleCircle L) (AddCircle.haarAddCircle (T := 1))
      (AddCircle.haarAddCircle (T := L)) := by
  apply AddMonoidHom.measurePreserving
    (f := (scaleCircle L).toAddMonoidHom)
    (AddCircle.continuous_equivAddCircle 1 L (by norm_num) hL.out.ne')
    (scaleCircle L).surjective
  simp

theorem scaleTorus_measurePreserving :
    MeasurePreserving (scaleTorus L) domainMeasure (periodMeasure L) := by
  exact measurePreserving_pi (fun _ : Fin 2 => AddCircle.haarAddCircle (T := 1))
    (fun _ : Fin 2 => AddCircle.haarAddCircle (T := L))
    (fun _ => scaleCircle_measurePreserving L)

theorem scaleTorus_symm_measurePreserving :
    MeasurePreserving (scaleTorus L).symm (periodMeasure L) domainMeasure :=
  (scaleTorus_measurePreserving L).symm (scaleTorus L).toMeasurableEquiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem integral_rescaling (f : PeriodDomain L → E) :
    (∫ q, f (scaleTorus L q) ∂domainMeasure) = ∫ y, f y ∂periodMeasure L :=
  MeasurePreserving.integral_comp' (f := (scaleTorus L).toMeasurableEquiv)
    (scaleTorus_measurePreserving L) f

theorem integral_unscaling (f : Domain → E) :
    (∫ y, f ((scaleTorus L).symm y) ∂periodMeasure L) = ∫ q, f q ∂domainMeasure :=
  MeasurePreserving.integral_comp' (f := (scaleTorus L).toMeasurableEquiv.symm)
    (scaleTorus_symm_measurePreserving L) f

abbrev PeriodField := Lp E 2 (periodMeasure L)

def pullField : PeriodField L (E := E) →ₗᵢ[ℝ] Field E :=
  Lp.compMeasurePreservingₗᵢ ℝ (scaleTorus L) (scaleTorus_measurePreserving L)

def pushField : Field E →ₗᵢ[ℝ] PeriodField L (E := E) :=
  Lp.compMeasurePreservingₗᵢ ℝ (scaleTorus L).symm (scaleTorus_symm_measurePreserving L)

theorem pullField_coe (f : PeriodField L (E := E)) :
    pullField L f =ᵐ[domainMeasure] fun q => f (scaleTorus L q) :=
  Lp.coeFn_compMeasurePreserving f (scaleTorus_measurePreserving L)

theorem pushField_coe (f : Field E) :
    pushField L f =ᵐ[periodMeasure L] fun y => f ((scaleTorus L).symm y) :=
  Lp.coeFn_compMeasurePreserving f (scaleTorus_symm_measurePreserving L)

theorem pullField_pushField (f : Field E) : pullField L (pushField L f) = f := by
  change Lp.compMeasurePreserving (scaleTorus L) (scaleTorus_measurePreserving L)
    (Lp.compMeasurePreserving (scaleTorus L).symm (scaleTorus_symm_measurePreserving L) f) = f
  rw [← Lp.compMeasurePreserving_comp_apply f
    (scaleTorus_symm_measurePreserving L) (scaleTorus_measurePreserving L)]
  have heq : (scaleTorus L).symm ∘ scaleTorus L = id := by
    funext q
    exact (scaleTorus L).symm_apply_apply q
  simp only [heq, Lp.compMeasurePreserving_id_apply]

theorem pushField_pullField (f : PeriodField L (E := E)) : pushField L (pullField L f) = f := by
  change Lp.compMeasurePreserving (scaleTorus L).symm (scaleTorus_symm_measurePreserving L)
    (Lp.compMeasurePreserving (scaleTorus L) (scaleTorus_measurePreserving L) f) = f
  rw [← Lp.compMeasurePreserving_comp_apply f
    (scaleTorus_measurePreserving L) (scaleTorus_symm_measurePreserving L)]
  have heq : scaleTorus L ∘ (scaleTorus L).symm = id := by
    funext q
    exact (scaleTorus L).apply_symm_apply q
  simp only [heq, Lp.compMeasurePreserving_id_apply]

def fieldRescaling : PeriodField L (E := E) ≃ₗᵢ[ℝ] Field E :=
  LinearIsometryEquiv.ofSurjective (pullField L)
    (fun f => ⟨pushField L f, pullField_pushField L f⟩)

def periodCoordinateFlow (i : Fin 2) (q : PeriodDomain L) (s : ℝ) : PeriodDomain L :=
  q + Pi.single i (s : AddCircle L)

theorem scaleTorus_coordinateFlow (i : Fin 2) (q : Domain) (s : ℝ) :
    scaleTorus L (coordinateFlow i q s) = periodCoordinateFlow L i (scaleTorus L q) (L * s) := by
  ext j
  change scaleCircle L (q j + (Pi.single i (s : UnitAddCircle) : Domain) j) =
    scaleCircle L (q j) + (Pi.single i (L * s : AddCircle L) : PeriodDomain L) j
  rw [map_add]
  by_cases hji : j = i
  · subst j
    simp [scaleCircle, mul_comm]
  · simp [Pi.single_eq_of_ne hji]

theorem scaleTorus_symm_coordinateFlow (i : Fin 2) (q : PeriodDomain L) (s : ℝ) :
    (scaleTorus L).symm (periodCoordinateFlow L i q s) =
      coordinateFlow i ((scaleTorus L).symm q) (s / L) := by
  apply (scaleTorus L).injective
  rw [(scaleTorus L).apply_symm_apply, scaleTorus_coordinateFlow,
    (scaleTorus L).apply_symm_apply]
  rw [mul_div_cancel₀ s hL.out.ne']

def pullContinuous (f : C(PeriodDomain L, E)) : C(Domain, E) :=
  f.comp ⟨scaleTorus L, (scaleTorus L).continuous⟩

def pushContinuous (f : C(Domain, E)) : C(PeriodDomain L, E) :=
  f.comp ⟨(scaleTorus L).symm, (scaleTorus L).symm.continuous⟩

omit [NormedSpace ℝ E] in
theorem pullContinuous_pushContinuous (f : C(Domain, E)) :
    pullContinuous L (pushContinuous L f) = f := by
  ext q
  exact congrArg f ((scaleTorus L).symm_apply_apply q)

omit [NormedSpace ℝ E] in
theorem pushContinuous_pullContinuous (f : C(PeriodDomain L, E)) :
    pushContinuous L (pullContinuous L f) = f := by
  ext q
  exact congrArg f ((scaleTorus L).apply_symm_apply q)

theorem pullContinuous_smul (c : ℝ) (f : C(PeriodDomain L, E)) :
    pullContinuous L (c • f) = c • pullContinuous L f := rfl

def periodContinuousField : C(PeriodDomain L, E) →L[ℝ] PeriodField L (E := E) :=
  ContinuousMap.toLp 2 (periodMeasure L) ℝ

theorem pullField_periodContinuousField (f : C(PeriodDomain L, E)) :
    pullField L (periodContinuousField L f) =
      ContinuousMap.toLp 2 domainMeasure ℝ (pullContinuous L f) := by
  apply Lp.ext
  filter_upwards
    [pullField_coe L (periodContinuousField L f),
      (scaleTorus_measurePreserving L).quasiMeasurePreserving.ae
        (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (periodMeasure L) f),
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure (pullContinuous L f)]
      with q hpull hperiod hunit
  change pullField L (periodContinuousField L f) q = _
  change periodContinuousField L f (scaleTorus L q) = f (scaleTorus L q) at hperiod
  rw [hpull, hperiod, hunit]
  rfl

theorem pullField_compLpL {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] F) (f : PeriodField L (E := E)) :
    pullField L (T.compLpL 2 (periodMeasure L) f) =
      T.compLpL 2 domainMeasure (pullField L f) := by
  apply Lp.ext
  filter_upwards
    [pullField_coe L (T.compLpL 2 (periodMeasure L) f),
      (scaleTorus_measurePreserving L).quasiMeasurePreserving.ae (T.coeFn_compLpL f),
      T.coeFn_compLpL (pullField L f), pullField_coe L f]
      with q hleft hperiod hright hf
  rw [hleft, hperiod, hright, hf]

def periodRealLift (f : C(PeriodDomain L, ℝ)) (x : Fin 2 → ℝ) : ℝ :=
  f (fun i => (x i : AddCircle L))

structure PeriodSmoothTest where
  value : C(PeriodDomain L, ℝ)
  derivative : Fin 2 → C(PeriodDomain L, ℝ)
  smooth : ContDiff ℝ ∞ (periodRealLift L value)
  hasPartial : ∀ i q,
    HasDerivAt (fun s : ℝ => value (periodCoordinateFlow L i q s)) (derivative i q) 0

def pullPeriodTest (test : PeriodSmoothTest L) : SmoothTest where
  value := pullContinuous L test.value
  derivative i := L • pullContinuous L (test.derivative i)
  smooth := by
    have heq : realLift (pullContinuous L test.value) =
        fun x : Fin 2 → ℝ => periodRealLift L test.value (fun i => L * x i) := by
      funext x
      change test.value (scaleTorus L (fun i => (x i : UnitAddCircle))) = _
      rw [scaleTorus_coe]
      rfl
    rw [heq]
    exact test.smooth.comp (by fun_prop)
  hasPartial i q := by
    have h := (test.hasPartial i (scaleTorus L q)).comp_of_eq 0
      ((hasDerivAt_id (0 : ℝ)).const_mul L) (by simp)
    convert h using 1
    · ext s
      change test.value (scaleTorus L (coordinateFlow i q s)) =
        test.value (periodCoordinateFlow L i (scaleTorus L q) (L * s))
      rw [scaleTorus_coordinateFlow]
    · simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_one]
      change L * test.derivative i (scaleTorus L q) = test.derivative i (scaleTorus L q) * L
      ring

def pushUnitTest (test : SmoothTest) : PeriodSmoothTest L where
  value := pushContinuous L test.value
  derivative i := L⁻¹ • pushContinuous L (test.derivative i)
  smooth := by
    have heq : periodRealLift L (pushContinuous L test.value) =
        fun x : Fin 2 → ℝ => realLift test.value (fun i => x i / L) := by
      funext x
      change test.value ((scaleTorus L).symm (fun i => (x i : AddCircle L))) = _
      rw [scaleTorus_symm_coe]
      rfl
    rw [heq]
    exact test.smooth.comp (by fun_prop)
  hasPartial i q := by
    have h := (test.hasPartial i ((scaleTorus L).symm q)).comp_of_eq 0
      ((hasDerivAt_id (0 : ℝ)).div_const L) (by simp)
    convert h using 1
    · ext s
      change test.value ((scaleTorus L).symm (periodCoordinateFlow L i q s)) =
        test.value (coordinateFlow i ((scaleTorus L).symm q) (s / L))
      rw [scaleTorus_symm_coordinateFlow]
    · change L⁻¹ * test.derivative i ((scaleTorus L).symm q) =
        test.derivative i ((scaleTorus L).symm q) * (1 / L)
      ring

abbrev PeriodScalarField := PeriodField L (E := ℝ)
abbrev PeriodPhysicalField := PeriodField L (E := PhysicalGradient)

def periodComponentField (i : Fin 2) (a : Fin 16) :
    PeriodPhysicalField L →L[ℝ] PeriodScalarField L :=
  (EuclideanSpace.proj (𝕜 := ℝ) (i, a)).compLpL 2 (periodMeasure L)

def PeriodHasWeakGradient (u : Fin 16 → PeriodScalarField L)
    (g : PeriodPhysicalField L) : Prop :=
  ∀ i a (test : PeriodSmoothTest L),
    inner ℝ (periodComponentField L i a g) (periodContinuousField L test.value) =
      -inner ℝ (u a) (periodContinuousField L (test.derivative i))

theorem pullField_periodComponentField (i : Fin 2) (a : Fin 16) (g : PeriodPhysicalField L) :
    pullField L (periodComponentField L i a g) = componentField i a (pullField L g) :=
  pullField_compLpL L _ g

theorem pullField_pushUnitTest_value (test : SmoothTest) :
    pullField L (periodContinuousField L (pushUnitTest L test).value) =
      continuousField test.value := by
  rw [pullField_periodContinuousField]
  change ContinuousMap.toLp 2 domainMeasure ℝ
    (pullContinuous L (pushContinuous L test.value)) = _
  rw [pullContinuous_pushContinuous]
  rfl

theorem pullField_pushUnitTest_derivative (test : SmoothTest) (i : Fin 2) :
    pullField L (periodContinuousField L ((pushUnitTest L test).derivative i)) =
      L⁻¹ • continuousField (test.derivative i) := by
  rw [pullField_periodContinuousField]
  change ContinuousMap.toLp 2 domainMeasure ℝ
    (pullContinuous L (L⁻¹ • pushContinuous L (test.derivative i))) = _
  rw [pullContinuous_smul, pullContinuous_pushContinuous, map_smul]
  rfl

theorem periodWeakGradient_pull {u : Fin 16 → PeriodScalarField L}
    {g : PeriodPhysicalField L} (hg : PeriodHasWeakGradient L u g) :
    HasWeakGradient (fun a => L⁻¹ • pullField L (u a)) (pullField L g) := by
  intro i a test
  have h := hg i a (pushUnitTest L test)
  rw [← (pullField L (E := ℝ)).inner_map_map
    (periodComponentField L i a g) (periodContinuousField L (pushUnitTest L test).value),
    ← (pullField L (E := ℝ)).inner_map_map (u a)
      (periodContinuousField L ((pushUnitTest L test).derivative i))] at h
  rw [pullField_periodComponentField, pullField_pushUnitTest_value,
    pullField_pushUnitTest_derivative, inner_smul_right] at h
  simpa only [real_inner_smul_left] using h

theorem periodWeakGradient_of_pull {u : Fin 16 → PeriodScalarField L}
    {g : PeriodPhysicalField L}
    (hg : HasWeakGradient (fun a => L⁻¹ • pullField L (u a)) (pullField L g)) :
    PeriodHasWeakGradient L u g := by
  intro i a test
  have h := hg i a (pullPeriodTest L test)
  change inner ℝ (componentField i a (pullField L g))
      (continuousField (pullContinuous L test.value)) =
    -inner ℝ (L⁻¹ • pullField L (u a))
      (continuousField (L • pullContinuous L (test.derivative i))) at h
  rw [map_smul, real_inner_smul_left, inner_smul_right,
    ← mul_assoc, inv_mul_cancel₀ hL.out.ne', one_mul] at h
  have hv : continuousField (pullContinuous L test.value) =
      pullField L (periodContinuousField L test.value) :=
    (pullField_periodContinuousField L test.value).symm
  have hd : continuousField (pullContinuous L (test.derivative i)) =
      pullField L (periodContinuousField L (test.derivative i)) :=
    (pullField_periodContinuousField L (test.derivative i)).symm
  rw [hv, hd, ← pullField_periodComponentField,
    (pullField L (E := ℝ)).inner_map_map,
    (pullField L (E := ℝ)).inner_map_map] at h
  exact h

theorem periodWeakGradient_iff (u : Fin 16 → PeriodScalarField L)
    (g : PeriodPhysicalField L) :
    PeriodHasWeakGradient L u g ↔
      HasWeakGradient (fun a => L⁻¹ • pullField L (u a)) (pullField L g) :=
  ⟨periodWeakGradient_pull L, periodWeakGradient_of_pull L⟩

def periodWeakGradientSpace : Submodule ℝ (PeriodPhysicalField L) where
  carrier := {g | ∃ u : Fin 16 → PeriodScalarField L, PeriodHasWeakGradient L u g}
  zero_mem' := by
    refine ⟨fun _ => 0, ?_⟩
    intro i a test
    simp [periodComponentField]
  add_mem' := by
    rintro g h ⟨u, hu⟩ ⟨v, hv⟩
    refine ⟨fun a => u a + v a, ?_⟩
    intro i a test
    simp only [map_add, inner_add_left]
    rw [hu, hv]
    ring
  smul_mem' := by
    rintro c g ⟨u, hu⟩
    refine ⟨fun a => c • u a, ?_⟩
    intro i a test
    simp only [map_smul, real_inner_smul_left]
    rw [hu]
    ring

theorem periodWeakGradientSpace_pull_iff (g : PeriodPhysicalField L) :
    g ∈ periodWeakGradientSpace L ↔ pullField L g ∈ weakGradientSpace := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨fun a => L⁻¹ • pullField L (u a), periodWeakGradient_pull L hu⟩
  · rintro ⟨u, hu⟩
    refine ⟨fun a => L • pushField L (u a), periodWeakGradient_of_pull L ?_⟩
    simpa only [map_smul, pullField_pushField, smul_smul,
      inv_mul_cancel₀ hL.out.ne', one_smul] using hu

def periodConstantField (F : PhysicalGradient) : PeriodPhysicalField L :=
  Lp.const 2 (periodMeasure L) F

theorem pullField_periodConstantField (F : PhysicalGradient) :
    pullField L (periodConstantField L F) = constantField F := by
  apply Lp.ext
  filter_upwards
    [pullField_coe L (periodConstantField L F),
      (scaleTorus_measurePreserving L).quasiMeasurePreserving.ae
        (Lp.coeFn_const 2 (periodMeasure L) F),
      Lp.coeFn_const 2 domainMeasure F] with q hpull hp hc
  change periodConstantField L F (scaleTorus L q) = F at hp
  change constantField F q = F at hc
  rw [hpull, hp, hc]

def periodFieldEnergy (B : PeriodPhysicalField L →L[ℝ] PeriodPhysicalField L)
    (F : PhysicalGradient) (g : PeriodPhysicalField L) : ℝ :=
  inner ℝ (B (periodConstantField L F + g)) (periodConstantField L F + g)

def periodWeakCellEnergy (B : PeriodPhysicalField L →L[ℝ] PeriodPhysicalField L)
    (F : PhysicalGradient) : ℝ :=
  sInf (periodFieldEnergy L B F '' (periodWeakGradientSpace L : Set (PeriodPhysicalField L)))

theorem periodFieldEnergy_transport
    (B : PeriodPhysicalField L →L[ℝ] PeriodPhysicalField L)
    (A : PhysicalField →L[ℝ] PhysicalField)
    (hA : ∀ f, pullField L (B f) = A (pullField L f))
    (F : PhysicalGradient) (g : PeriodPhysicalField L) :
    periodFieldEnergy L B F g = fieldEnergy A F (pullField L g) := by
  rw [periodFieldEnergy, ← (pullField L (E := PhysicalGradient)).inner_map_map,
    hA, map_add, pullField_periodConstantField]
  rfl

theorem periodWeakCellEnergy_transport
    (B : PeriodPhysicalField L →L[ℝ] PeriodPhysicalField L)
    (A : PhysicalField →L[ℝ] PhysicalField)
    (hA : ∀ f, pullField L (B f) = A (pullField L f))
    (F : PhysicalGradient) :
    periodWeakCellEnergy L B F = sobolevCellEnergy A F := by
  rw [sobolevCellEnergy_eq_weakCellEnergy]
  apply congrArg sInf
  ext r
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨pullField L g, (periodWeakGradientSpace_pull_iff L g).mp hg,
      (periodFieldEnergy_transport L B A hA F g).symm⟩
  · rintro ⟨g, hg, rfl⟩
    refine ⟨pushField L g, (periodWeakGradientSpace_pull_iff L _).mpr ?_, ?_⟩
    · rw [pullField_pushField]
      exact hg
    · rw [periodFieldEnergy_transport L B A hA F, pullField_pushField]

def rescaledLaw (A : PhysicalField →L[ℝ] PhysicalField) :
    PeriodPhysicalField L →L[ℝ] PeriodPhysicalField L :=
  (pushField L).toContinuousLinearMap.comp (A.comp (pullField L).toContinuousLinearMap)

theorem rescaledLaw_pull (A : PhysicalField →L[ℝ] PhysicalField)
    (f : PeriodPhysicalField L) :
    pullField L (rescaledLaw L A f) = A (pullField L f) :=
  pullField_pushField L _

theorem rescaledLaw_cellEnergy (A : PhysicalField →L[ℝ] PhysicalField) (F : PhysicalGradient) :
    periodWeakCellEnergy L (rescaledLaw L A) F = sobolevCellEnergy A F :=
  periodWeakCellEnergy_transport L _ A (rescaledLaw_pull L A) F

theorem rescaledLaw_coe (A : PhysicalField →L[ℝ] PhysicalField)
    (a : Domain → PhysicalGradient → PhysicalGradient)
    (hA : ∀ f : PhysicalField, A f =ᵐ[domainMeasure] fun q => a q (f q))
    (f : PeriodPhysicalField L) :
    rescaledLaw L A f =ᵐ[periodMeasure L]
      fun y => a ((scaleTorus L).symm y) (f y) := by
  filter_upwards
    [pushField_coe L (A (pullField L f)),
      (scaleTorus_symm_measurePreserving L).quasiMeasurePreserving.ae (hA (pullField L f)),
      (scaleTorus_symm_measurePreserving L).quasiMeasurePreserving.ae (pullField_coe L f)]
      with y hpush hcoeff hpull
  change rescaledLaw L A f y = A (pullField L f) ((scaleTorus L).symm y) at hpush
  rw [hpush, hcoeff, hpull, (scaleTorus L).apply_symm_apply]

theorem periodVolume_eq_smul_normalized :
    (volume : Measure (PeriodDomain L)) = (ENNReal.ofReal L) ^ 2 • periodMeasure L := by
  change Measure.pi (fun _ : Fin 2 => (volume : Measure (AddCircle L))) = _
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, periodMeasure, Measure.pi_pi]
  simp_rw [AddCircle.volume_eq_smul_haarAddCircle, Measure.smul_apply]
  norm_num [Fin.prod_univ_succ]
  ring

def periodCube : Set (Fin 2 → ℝ) := Set.univ.pi (fun _ => Set.Ioc (0 : ℝ) L)

def periodQuotient (x : Fin 2 → ℝ) : PeriodDomain L := fun i => (x i : AddCircle L)

theorem periodQuotient_measurePreserving :
    MeasurePreserving (periodQuotient L)
      ((volume : Measure (Fin 2 → ℝ)).restrict (periodCube L))
      (volume : Measure (PeriodDomain L)) := by
  change MeasurePreserving (fun x : Fin 2 → ℝ => fun i => (x i : AddCircle L))
    ((Measure.pi (fun _ : Fin 2 => (volume : Measure ℝ))).restrict
      (Set.univ.pi (fun _ => Set.Ioc (0 : ℝ) L)))
    (Measure.pi (fun _ : Fin 2 => (volume : Measure (AddCircle L))))
  rw [Measure.restrict_pi_pi]
  apply measurePreserving_pi
  intro i
  simpa only [zero_add] using AddCircle.measurePreserving_mk L 0

theorem normalized_period_integral_eq_cube
    (f : PeriodDomain L → E) (hf : Integrable f (volume : Measure (PeriodDomain L))) :
    (∫ y, f y ∂periodMeasure L) =
      (L ^ 2)⁻¹ • ∫ x in periodCube L, f (periodQuotient L x) := by
  have hm := periodQuotient_measurePreserving L
  have hfmap : AEStronglyMeasurable f
      (Measure.map (periodQuotient L) ((volume : Measure (Fin 2 → ℝ)).restrict (periodCube L))) := by
    rw [hm.map_eq]
    exact hf.aestronglyMeasurable
  have hi := integral_map hm.aemeasurable hfmap
  rw [hm.map_eq, periodVolume_eq_smul_normalized, integral_smul_measure,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hL.out.le] at hi
  have hne : L ^ 2 ≠ 0 := pow_ne_zero 2 hL.out.ne'
  calc
    (∫ y, f y ∂periodMeasure L) =
        (L ^ 2)⁻¹ • ((L ^ 2) • ∫ y, f y ∂periodMeasure L) :=
      (inv_smul_smul₀ hne _).symm
    _ = _ := congrArg (fun v : E => (L ^ 2)⁻¹ • v) hi

def periodOpenCube : Set (Fin 2 → ℝ) := Set.univ.pi (fun _ => Set.Ioo (0 : ℝ) L)

omit hL in
theorem periodCube_ae_openCube :
    periodCube L =ᵐ[(volume : Measure (Fin 2 → ℝ))] periodOpenCube L := by
  have hne : ∀ᵐ x : Fin 2 → ℝ ∂(volume : Measure (Fin 2 → ℝ)), ∀ i, x i ≠ L := by
    apply ae_all_iff.mpr
    intro i
    exact Measure.ae_eval_ne (μ := fun _ : Fin 2 => (volume : Measure ℝ)) i L
  filter_upwards [hne] with x hx
  simp only [periodCube, periodOpenCube, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_Ioc, Set.mem_Ioo]
  apply propext
  apply forall_congr'
  intro i
  exact ⟨fun h => ⟨h.1, lt_of_le_of_ne h.2 (hx i)⟩, fun h => ⟨h.1, h.2.le⟩⟩

/-- The normalized mean equals the open-square Lebesgue mean. -/
theorem normalized_period_integral_eq_openCube
    (f : PeriodDomain L → E) (hf : Integrable f (volume : Measure (PeriodDomain L))) :
    (∫ y, f y ∂periodMeasure L) =
      (L ^ 2)⁻¹ • ∫ x in periodOpenCube L, f (periodQuotient L x) := by
  rw [normalized_period_integral_eq_cube L f hf]
  congr 1
  exact setIntegral_congr_set (periodCube_ae_openCube L)

end HierarchicalLaminates.Periodic
