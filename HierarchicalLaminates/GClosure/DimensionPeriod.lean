module

public import HierarchicalLaminates.GClosure.DimensionAll

/-! Weak periodic cell energies for arbitrary component indices on a period-2π cell. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open MeasureTheory HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material HierarchicalLaminates.Lamination
  HierarchicalLaminates.Homogenization

variable (L : ℝ) [hL : Fact (0 < L)]

def GenericPeriodHasWeakGradient {α : Type*} (u : α → PeriodScalarField L)
    (g : ComponentIndex α → PeriodScalarField L) : Prop :=
  ∀ i a (test : PeriodSmoothTest L),
    inner ℝ (g (i,a)) (periodContinuousField L test.value) =
      -inner ℝ (u a) (periodContinuousField L (test.derivative i))

structure PeriodWeakPotential (α : Type*) where
  potential : α → PeriodScalarField L
  gradient : ComponentIndex α → PeriodScalarField L
  weak : GenericPeriodHasWeakGradient L potential gradient

theorem genericPeriodWeak_pull {α : Type*} {u : α → PeriodScalarField L}
    {g : ComponentIndex α → PeriodScalarField L} (hg : GenericPeriodHasWeakGradient L u g)
    (i : Fin 2) (a : α) (test : SmoothTest) :
    inner ℝ (pullField L (g (i,a))) (continuousField test.value) =
      -inner ℝ (L⁻¹ • pullField L (u a)) (continuousField (test.derivative i)) := by
  have h := hg i a (pushUnitTest L test)
  rw [← (pullField L (E := ℝ)).inner_map_map (g (i,a))
      (periodContinuousField L (pushUnitTest L test).value),
    ← (pullField L (E := ℝ)).inner_map_map (u a)
      (periodContinuousField L ((pushUnitTest L test).derivative i)),
    pullField_pushUnitTest_value,pullField_pushUnitTest_derivative,inner_smul_right] at h
  simpa only [real_inner_smul_left] using h

theorem genericPeriodWeak_of_pull {α : Type*} {u : α → PeriodScalarField L}
    {g : ComponentIndex α → PeriodScalarField L}
    (hg : ∀ i a (test : SmoothTest),
      inner ℝ (pullField L (g (i,a))) (continuousField test.value) =
        -inner ℝ (L⁻¹ • pullField L (u a)) (continuousField (test.derivative i))) :
    GenericPeriodHasWeakGradient L u g := by
  intro i a test
  have h := hg i a (pullPeriodTest L test)
  change inner ℝ (pullField L (g (i,a))) (continuousField (pullContinuous L test.value)) =
    -inner ℝ (L⁻¹ • pullField L (u a))
      (continuousField (L • pullContinuous L (test.derivative i))) at h
  rw [map_smul,real_inner_smul_left,inner_smul_right,← mul_assoc,
    inv_mul_cancel₀ hL.out.ne',one_mul] at h
  have hv : continuousField (pullContinuous L test.value) =
      pullField L (periodContinuousField L test.value) :=
    (pullField_periodContinuousField L test.value).symm
  have hd : continuousField (pullContinuous L (test.derivative i)) =
      pullField L (periodContinuousField L (test.derivative i)) :=
    (pullField_periodContinuousField L (test.derivative i)).symm
  rw [hv,hd,(pullField L (E := ℝ)).inner_map_map,
    (pullField L (E := ℝ)).inner_map_map] at h
  exact h

def PeriodWeakPotential.pull {α : Type*} (u : PeriodWeakPotential L α) : WeakPotential α where
  potential a := L⁻¹ • pullField L (u.potential a)
  gradient c := pullField L (u.gradient c)
  weak := genericPeriodWeak_pull L u.weak

def WeakPotential.pushPeriod {α : Type*} (u : WeakPotential α) : PeriodWeakPotential L α where
  potential a := L • pushField L (u.potential a)
  gradient c := pushField L (u.gradient c)
  weak := by
    apply genericPeriodWeak_of_pull
    intro i a test
    simpa only [map_smul,pullField_pushField,smul_smul,inv_mul_cancel₀ hL.out.ne',one_smul] using
      u.weak i a test

theorem pull_pushPeriod {α : Type*} (u : WeakPotential α) : (u.pushPeriod L).pull L = u := by
  apply WeakPotential.ext
  · funext a
    simp [WeakPotential.pushPeriod,PeriodWeakPotential.pull,map_smul,pullField_pushField,
      smul_smul,inv_mul_cancel₀ hL.out.ne']
  · funext c
    exact pullField_pushField L (u.gradient c)

def genericPeriodConstant (c : ℝ) : PeriodScalarField L := Lp.const 2 (periodMeasure L) c

theorem genericPeriodConstant_pull (c : ℝ) :
    pullField L (genericPeriodConstant L c) = constantField c := by
  apply Lp.ext
  filter_upwards [pullField_coe L (genericPeriodConstant L c),
    (scaleTorus_measurePreserving L).quasiMeasurePreserving.ae
      (Lp.coeFn_const 2 (periodMeasure L) c),Lp.coeFn_const 2 domainMeasure c]
    with q hpull hp hc
  change genericPeriodConstant L c (scaleTorus L q) = c at hp
  change constantField c q = c at hc
  rw [hpull,hp,hc]

def periodScalarLaw (c₀ c₁ : ℝ) (b : PhaseFraction) (f : PeriodScalarField L) :
    PeriodScalarField L := pushField L (scalarLaw c₀ c₁ b (pullField L f))

theorem periodScalarLaw_coe (c₀ c₁ : ℝ) (b : PhaseFraction) (f : PeriodScalarField L) :
    periodScalarLaw L c₀ c₁ b f =ᵐ[periodMeasure L] fun y =>
      (c₀+b.value ((scaleTorus L).symm y)*(c₁-c₀))*f y := by
  filter_upwards [pushField_coe L (scalarLaw c₀ c₁ b (pullField L f)),
    (scaleTorus_symm_measurePreserving L).quasiMeasurePreserving.ae
      (scalarLaw_coe c₀ c₁ b (pullField L f)),
    (scaleTorus_symm_measurePreserving L).quasiMeasurePreserving.ae (pullField_coe L f)]
    with y hpush hcoeff hpull
  change periodScalarLaw L c₀ c₁ b f y = _ at hpush
  rw [hpush,hcoeff,hpull,(scaleTorus L).apply_symm_apply]

def periodAffineComponent {α : Type*} (F : Gradient α) (u : PeriodWeakPotential L α)
    (c : ComponentIndex α) : PeriodScalarField L := genericPeriodConstant L (F c) + u.gradient c

def genericPeriodFieldEnergy {α : Type*} [Fintype α] (L₀ L₁ : Tensor α) (b : PhaseFraction)
    (F : Gradient α) (u : PeriodWeakPotential L α) : ℝ :=
  ∑ c : ComponentIndex α, ∑ d : ComponentIndex α,
    inner ℝ (periodScalarLaw L (L₀ c d) (L₁ c d) b (periodAffineComponent L F u d))
      (periodAffineComponent L F u c)

def genericPeriodCellEnergy {α : Type*} [Fintype α] (L₀ L₁ : Tensor α) (b : PhaseFraction)
    (F : Gradient α) : ℝ := sInf (Set.range (genericPeriodFieldEnergy L L₀ L₁ b F))

theorem periodScalarLaw_inner_integral (c₀ c₁ : ℝ) (b : PhaseFraction)
    (f g : PeriodScalarField L) :
    inner ℝ (periodScalarLaw L c₀ c₁ b f) g =
      ∫ y, (c₀+b.value ((scaleTorus L).symm y)*(c₁-c₀))*f y*g y ∂periodMeasure L := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [periodScalarLaw_coe L c₀ c₁ b f] with y hy
  rw [hy]
  simp only [Real.inner_apply]

theorem periodScalarLaw_integrable (c₀ c₁ : ℝ) (b : PhaseFraction)
    (f g : PeriodScalarField L) :
    Integrable (fun y => (c₀+b.value ((scaleTorus L).symm y)*(c₁-c₀))*f y*g y)
      (periodMeasure L) := by
  apply (L2.integrable_inner (periodScalarLaw L c₀ c₁ b f) g).congr
  filter_upwards [periodScalarLaw_coe L c₀ c₁ b f] with y hy
  rw [hy]
  simp only [Real.inner_apply]

/-- The period-cell energy uses the transported binary coefficient and weak derivatives. -/
theorem genericPeriodFieldEnergy_eq_integral {α : Type*} [Fintype α]
    (L₀ L₁ : Tensor α) (b : PhaseFraction) (F : Gradient α) (u : PeriodWeakPotential L α) :
    genericPeriodFieldEnergy L L₀ L₁ b F u =
      ∫ y, quadraticEnergy (L₀+b.value ((scaleTorus L).symm y) • (L₁-L₀))
        (fun c => F c + u.gradient c y) ∂periodMeasure L := by
  have he (c : ComponentIndex α) : periodAffineComponent L F u c =ᵐ[periodMeasure L]
      fun y => F c+u.gradient c y := by
    filter_upwards [Lp.coeFn_add (genericPeriodConstant L (F c)) (u.gradient c),
      Lp.coeFn_const 2 (periodMeasure L) (F c)] with y hadd hc
    change genericPeriodConstant L (F c) y = F c at hc
    rw [periodAffineComponent,hadd]
    simp only [Pi.add_apply]
    rw [hc]
  have hs : (∑ c : ComponentIndex α, ∑ d : ComponentIndex α,
      inner ℝ (periodScalarLaw L (L₀ c d) (L₁ c d) b (periodAffineComponent L F u d))
        (periodAffineComponent L F u c)) =
      ∫ y, ∑ c : ComponentIndex α, ∑ d : ComponentIndex α,
        (L₀ c d+b.value ((scaleTorus L).symm y)*(L₁ c d-L₀ c d))*
          periodAffineComponent L F u d y*periodAffineComponent L F u c y ∂periodMeasure L := by
    simp_rw [periodScalarLaw_inner_integral]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro c _
      rw [integral_finsetSum]
      exact fun d _ => periodScalarLaw_integrable _ _ _ _ _ _
    · intro c _
      exact integrable_finsetSum _ (fun d _ => periodScalarLaw_integrable _ _ _ _ _ _)
  rw [genericPeriodFieldEnergy,hs]
  apply integral_congr_ae
  have heall : ∀ᵐ y ∂periodMeasure L, ∀ c, periodAffineComponent L F u c y = F c+u.gradient c y := by
    simp only [Filter.eventually_all]
    exact he
  filter_upwards [heall] with y hy
  simp only [hy,quadraticEnergy,dotProduct,Matrix.mulVec,Matrix.add_apply,
    Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem genericPeriodFieldEnergy_pull {α : Type*} [Fintype α]
    (L₀ L₁ : Tensor α) (b : PhaseFraction) (F : Gradient α) (u : PeriodWeakPotential L α) :
    genericPeriodFieldEnergy L L₀ L₁ b F u = genericFieldEnergy L₀ L₁ b F (u.pull L) := by
  unfold genericPeriodFieldEnergy genericFieldEnergy
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  rw [← (pullField L (E := ℝ)).inner_map_map,
    periodScalarLaw,pullField_pushField]
  simp only [periodAffineComponent,map_add,genericPeriodConstant_pull,
    affineComponent,PeriodWeakPotential.pull]

theorem genericPeriodCellEnergy_transport {α : Type*} [Fintype α]
    (L₀ L₁ : Tensor α) (b : PhaseFraction) (F : Gradient α) :
    genericPeriodCellEnergy L L₀ L₁ b F = genericCellEnergy L₀ L₁ b F := by
  unfold genericPeriodCellEnergy genericCellEnergy
  apply congrArg sInf
  ext E
  constructor
  · rintro ⟨u,rfl⟩
    exact ⟨u.pull L,(genericPeriodFieldEnergy_pull L L₀ L₁ b F u).symm⟩
  · rintro ⟨u,rfl⟩
    refine ⟨u.pushPeriod L,?_⟩
    rw [genericPeriodFieldEnergy_pull,pull_pushPeriod]

theorem all_m_counterexample_manuscript (m : ℕ) (hm : 16 ≤ m)
    (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    ∃ b : PhaseFraction,
      Measurable (transportedIndicator b) ∧
      (∀ y, transportedIndicator b y = 0 ∨ transportedIndicator b y = 1) ∧
      ((manuscriptPeriod^2)⁻¹ * ∫ x in periodOpenCube manuscriptPeriod,
        transportedIndicator b (periodQuotient manuscriptPeriod x)) = θ ∧
      (∀ F : Gradient (Fin m), quadraticEnergy (dimensionEffective m hm b) F =
        genericPeriodCellEnergy manuscriptPeriod (dimensionPhaseZero m hm) (dimensionPhaseOne m hm) b F) ∧
      0 < loadingDifference (dimensionXi m hm) (dimensionEta m hm) (dimensionEffective m hm b) ∧
      dimensionEffective m hm b ∉ closure (allFiniteLaminates
        (dimensionPhaseZero m hm) (dimensionPhaseOne m hm)) := by
  obtain ⟨b,hb,hmn,he,hp,hn⟩ := all_m_counterexample m hm θ hθ₀ hθ₁
  refine ⟨b,transportedIndicator_measurable b,transportedIndicator_values b hb,
    (transportedIndicator_mean_openCube b).trans hmn,?_,hp,hn⟩
  intro F
  rw [genericPeriodCellEnergy_transport]
  exact he F

end HierarchicalLaminates.GClosure
