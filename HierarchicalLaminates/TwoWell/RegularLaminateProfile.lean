module

public import HierarchicalLaminates.Composition.LocalizedPotentialLift
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Regular periodic laminate profiles

A smooth transition rounds the corners of a periodic scalar primitive. The
gradient is exactly constant on each bulk region and uniformly bounded as the
transition width tends to zero. These identities produce C¹ periodic
potentials for the Jensen tests in `LaminateJensen`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.TwoWell

open MeasureTheory Set Filter HierarchicalLaminates.Composition
  HierarchicalLaminates.Periodic HierarchicalLaminates.Homogenization
open scoped Topology

theorem smoothTransition_one_sub (x : ℝ) :
    Real.smoothTransition (1-x) = 1-Real.smoothTransition x := by
  have hd := (Real.smoothTransition.pos_denom x).ne'
  have hd' : expNegInvGlue (1-x)+expNegInvGlue x ≠ 0 := by
    simpa only [add_comm] using hd
  unfold Real.smoothTransition
  rw [sub_sub_cancel]
  field_simp [hd,hd']
  ring

def roundedCornerSlope (δ x : ℝ) : ℝ := Real.smoothTransition ((x+δ)/(2*δ))

theorem roundedCornerSlope_continuous (δ : ℝ) : Continuous (roundedCornerSlope δ) := by
  unfold roundedCornerSlope
  fun_prop

theorem roundedCornerSlope_mem (δ x : ℝ) : roundedCornerSlope δ x ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩

theorem roundedCornerSlope_zero {δ x : ℝ} (hδ : 0 < δ) (hx : x ≤ -δ) :
    roundedCornerSlope δ x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

theorem roundedCornerSlope_one {δ x : ℝ} (hδ : 0 < δ) (hx : δ ≤ x) :
    roundedCornerSlope δ x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  exact (le_div_iff₀ (by positivity : 0 < 2*δ)).mpr (by linarith)

theorem roundedCornerSlope_neg {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    roundedCornerSlope δ (-x) = 1-roundedCornerSlope δ x := by
  have heq : (-x+δ)/(2*δ) = 1-(x+δ)/(2*δ) := by
    field_simp
    ring
  change Real.smoothTransition ((-x+δ)/(2*δ)) =
    1-Real.smoothTransition ((x+δ)/(2*δ))
  rw [heq,smoothTransition_one_sub]

def cornerPrimitive (δ x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, roundedCornerSlope δ t

theorem cornerPrimitive_hasDerivAt (δ x : ℝ) :
    HasDerivAt (cornerPrimitive δ) (roundedCornerSlope δ x) x := by
  exact intervalIntegral.integral_hasDerivAt_right
    ((roundedCornerSlope_continuous δ).intervalIntegrable 0 x)
    (roundedCornerSlope_continuous δ).stronglyMeasurable.stronglyMeasurableAtFilter
    (roundedCornerSlope_continuous δ).continuousAt

theorem cornerPrimitive_continuous (δ : ℝ) : Continuous (cornerPrimitive δ) := by
  exact (show Differentiable ℝ (cornerPrimitive δ) from
    fun x => (cornerPrimitive_hasDerivAt δ x).differentiableAt).continuous

theorem cornerPrimitive_reflection {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    cornerPrimitive δ x - cornerPrimitive δ (-x) = x := by
  let f : ℝ → ℝ := fun y => cornerPrimitive δ y-cornerPrimitive δ (-y)-y
  have hd (y : ℝ) : HasDerivAt f 0 y := by
    have hneg := (cornerPrimitive_hasDerivAt δ (-y)).comp y (hasDerivAt_neg y)
    have h := ((cornerPrimitive_hasDerivAt δ y).sub hneg).sub (hasDerivAt_id y)
    convert h using 1
    · rfl
    · rw [roundedCornerSlope_neg hδ]
      ring
  have heq := is_const_of_deriv_eq_zero (fun y => (hd y).differentiableAt)
    (fun y => (hd y).deriv) x 0
  change cornerPrimitive δ x-cornerPrimitive δ (-x)-x =
    cornerPrimitive δ 0-cornerPrimitive δ (-0)-0 at heq
  simp only [neg_zero,sub_self] at heq
  linarith

def roundedCorner (δ x : ℝ) : ℝ := cornerPrimitive δ x-cornerPrimitive δ (-δ)

theorem roundedCorner_hasDerivAt (δ x : ℝ) :
    HasDerivAt (roundedCorner δ) (roundedCornerSlope δ x) x :=
  (cornerPrimitive_hasDerivAt δ x).sub_const _

theorem roundedCorner_continuous (δ : ℝ) : Continuous (roundedCorner δ) :=
  (cornerPrimitive_continuous δ).sub continuous_const

theorem roundedCorner_zero {δ x : ℝ} (hδ : 0 < δ) (hx : x ≤ -δ) :
    roundedCorner δ x = 0 := by
  rw [roundedCorner,cornerPrimitive,cornerPrimitive,
    intervalIntegral.integral_interval_sub_left
      ((roundedCornerSlope_continuous δ).intervalIntegrable 0 x)
      ((roundedCornerSlope_continuous δ).intervalIntegrable 0 (-δ))]
  calc
    _ = ∫ _t in (-δ)..x, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_ge hx] at ht
      exact roundedCornerSlope_zero hδ ht.2
    _ = 0 := by simp

theorem roundedCorner_eq_self {δ x : ℝ} (hδ : 0 < δ) (hx : δ ≤ x) :
    roundedCorner δ x = x := by
  have href := cornerPrimitive_reflection hδ δ
  have hdifference : cornerPrimitive δ x-cornerPrimitive δ δ = x-δ := by
    rw [cornerPrimitive,cornerPrimitive,
      intervalIntegral.integral_interval_sub_left
        ((roundedCornerSlope_continuous δ).intervalIntegrable 0 x)
        ((roundedCornerSlope_continuous δ).intervalIntegrable 0 δ)]
    calc
      _ = ∫ _t in δ..x, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hx] at ht
        exact roundedCornerSlope_one hδ ht.1
      _ = x-δ := by simp
  dsimp [roundedCorner]
  linarith

def rawLaminateValue (a δ y : ℝ) : ℝ := (1-a)*y-roundedCorner δ (y-a)

def rawLaminateSlope (a δ y : ℝ) : ℝ := 1-a-roundedCornerSlope δ (y-a)

theorem rawLaminate_hasDerivAt (a δ y : ℝ) :
    HasDerivAt (rawLaminateValue a δ) (rawLaminateSlope a δ y) y := by
  convert ((hasDerivAt_id y).const_mul (1-a)).sub
    ((roundedCorner_hasDerivAt δ (y-a)).comp y ((hasDerivAt_id y).sub_const a)) using 1
  · rfl
  · simp [rawLaminateSlope]

theorem rawLaminateValue_continuous (a δ : ℝ) : Continuous (rawLaminateValue a δ) := by
  exact (show Differentiable ℝ (rawLaminateValue a δ) from
    fun y => (rawLaminate_hasDerivAt a δ y).differentiableAt).continuous

theorem rawLaminateSlope_continuous (a δ : ℝ) : Continuous (rawLaminateSlope a δ) := by
  exact continuous_const.sub ((roundedCornerSlope_continuous δ).comp
    (continuous_id.sub continuous_const))

theorem rawLaminateValue_left {a δ y : ℝ} (hδ : 0 < δ) (hy : y ≤ a-δ) :
    rawLaminateValue a δ y = (1-a)*y := by
  rw [rawLaminateValue,roundedCorner_zero hδ (by linarith),sub_zero]

theorem rawLaminateValue_right {a δ y : ℝ} (hδ : 0 < δ) (hy : a+δ ≤ y) :
    rawLaminateValue a δ y = a*(1-y) := by
  rw [rawLaminateValue,roundedCorner_eq_self hδ (by linarith)]
  ring

theorem rawLaminateSlope_left {a δ y : ℝ} (hδ : 0 < δ) (hy : y ≤ a-δ) :
    rawLaminateSlope a δ y = 1-a := by
  rw [rawLaminateSlope,roundedCornerSlope_zero hδ (by linarith),sub_zero]

theorem rawLaminateSlope_right {a δ y : ℝ} (hδ : 0 < δ) (hy : a+δ ≤ y) :
    rawLaminateSlope a δ y = -a := by
  rw [rawLaminateSlope,roundedCornerSlope_one hδ (by linarith)]
  ring

def laminateProfileValue (a δ y : ℝ) : ℝ :=
  rawSlabCutoff 1 δ y*rawLaminateValue a δ y

def laminateProfileSlope (a δ y : ℝ) : ℝ :=
  rawSlabCutoffDerivative 1 δ y*rawLaminateValue a δ y+
    rawSlabCutoff 1 δ y*rawLaminateSlope a δ y

theorem laminateProfile_hasDerivAt (a δ y : ℝ) :
    HasDerivAt (laminateProfileValue a δ) (laminateProfileSlope a δ y) y :=
  (rawSlabCutoff_hasDerivAt 1 δ y).mul (rawLaminate_hasDerivAt a δ y)

theorem laminateProfileValue_continuous (a δ : ℝ) :
    Continuous (laminateProfileValue a δ) :=
  ((rawSlabCutoff_contDiff 1 δ).continuous).mul (rawLaminateValue_continuous a δ)

theorem laminateProfileSlope_continuous (a δ : ℝ) :
    Continuous (laminateProfileSlope a δ) :=
  ((rawSlabCutoffDerivative_continuous 1 δ).mul (rawLaminateValue_continuous a δ)).add
    ((rawSlabCutoff_contDiff 1 δ).continuous.mul (rawLaminateSlope_continuous a δ))

theorem laminateProfileValue_zero {a δ y : ℝ} (hδ : 0 < δ)
    (hy : y ∉ Icc δ (1-δ)) : laminateProfileValue a δ y = 0 := by
  have hη : rawSlabCutoff 1 δ y = 0 := by
    rcases not_and_or.mp hy with h | h
    · exact rawSlabCutoff_zero_left 1 hδ (le_of_lt (lt_of_not_ge h))
    · exact rawSlabCutoff_zero_right hδ (le_of_lt (lt_of_not_ge h))
  simp only [laminateProfileValue,hη,zero_mul]

theorem laminateProfileSlope_zero {a δ y : ℝ} (hδ : 0 < δ)
    (hy : y ∉ Icc δ (1-δ)) : laminateProfileSlope a δ y = 0 := by
  have hη : rawSlabCutoff 1 δ y = 0 := by
    rcases not_and_or.mp hy with h | h
    · exact rawSlabCutoff_zero_left 1 hδ (le_of_lt (lt_of_not_ge h))
    · exact rawSlabCutoff_zero_right hδ (le_of_lt (lt_of_not_ge h))
  simp only [laminateProfileSlope,hη,rawSlabCutoffDerivative_zero_of_zero hη,
    zero_mul,add_zero]

theorem laminateProfileSlope_first {a δ y : ℝ} (hδ : 0 < δ)
    (ha : a+δ ≤ 1) (hy : y ∈ Icc (2*δ) (a-δ)) :
    laminateProfileSlope a δ y = 1-a := by
  have hη : rawSlabCutoff 1 δ y = 1 := rawSlabCutoff_one hδ hy.1 (by linarith [hy.2])
  simp only [laminateProfileSlope,rawSlabCutoffDerivative_zero_of_one hη,hη,
    zero_mul,one_mul,zero_add,rawLaminateSlope_left hδ hy.2]

theorem laminateProfileSlope_second {a δ y : ℝ} (hδ : 0 < δ)
    (ha : δ ≤ a) (hy : y ∈ Icc (a+δ) (1-2*δ)) :
    laminateProfileSlope a δ y = -a := by
  have hη : rawSlabCutoff 1 δ y = 1 := rawSlabCutoff_one hδ (by linarith [hy.1]) hy.2
  simp only [laminateProfileSlope,rawSlabCutoffDerivative_zero_of_one hη,hη,
    zero_mul,one_mul,zero_add,rawLaminateSlope_right hδ hy.1]

def scalarProfileValue (a δ : ℝ) (hδ : 0 < δ) (_hδ₁ : δ < 1) : C(Domain,ℝ) :=
  ⟨liftSlabFamily (fun _ y => laminateProfileValue a δ y),
    liftSlabFamily_continuous hδ (by linarith)
      ((laminateProfileValue_continuous a δ).comp continuous_snd)
      (fun _ _ hy => laminateProfileValue_zero hδ hy)⟩

def scalarProfileSlope (a δ : ℝ) (hδ : 0 < δ) (_hδ₁ : δ < 1) : C(Domain,ℝ) :=
  ⟨liftSlabFamily (fun _ y => laminateProfileSlope a δ y),
    liftSlabFamily_continuous hδ (by linarith)
      ((laminateProfileSlope_continuous a δ).comp continuous_snd)
      (fun _ _ hy => laminateProfileSlope_zero hδ hy)⟩

theorem scalarProfileValue_hasPartial_zero {a δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ < 1)
    (i : Fin 2) (q : Domain) :
    HasDerivAt (fun s : ℝ => scalarProfileValue a δ hδ hδ₁ (coordinateFlow i q s))
      (if i = 0 then 0 else scalarProfileSlope a δ hδ hδ₁ q) 0 := by
  by_cases hq : q 1 = 0
  · have hev : (fun s : ℝ => scalarProfileValue a δ hδ hδ₁ (coordinateFlow i q s))
        =ᶠ[𝓝 0] (fun _ => 0) := by
      have hc : Continuous (coordinateFlow i q) :=
        continuous_const.add ((continuous_single i).comp (AddCircle.continuous_mk' (1 : ℝ)))
      have ht : Tendsto (coordinateFlow i q) (𝓝 (0 : ℝ)) (𝓝 q) := by
        have ht : Tendsto (coordinateFlow i q) (𝓝 (0 : ℝ))
            (𝓝 (coordinateFlow i q 0)) := hc.continuousAt
        simpa only [HierarchicalLaminates.Fourier.coordinateFlow_zero] using ht
      exact ht.eventually (liftSlabFamily_eventually_zero hδ (by linarith)
        (fun _ _ hy => laminateProfileValue_zero hδ hy) hq)
    have hs : scalarProfileSlope a δ hδ hδ₁ q = 0 := by
      change laminateProfileSlope a δ (circleRepresentative (q 1)) = 0
      rw [hq,circleRepresentative_zero]
      exact laminateProfileSlope_zero hδ (fun h => (not_le.mpr hδ) h.1)
    simpa only [hs,ite_self] using
      (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hev
  · fin_cases i
    · have heq : (fun s : ℝ => scalarProfileValue a δ hδ hδ₁ (coordinateFlow 0 q s)) =
          (fun _ => scalarProfileValue a δ hδ hδ₁ q) := by
        funext s
        simp [scalarProfileValue,liftSlabFamily,coordinateFlow_eval]
      change HasDerivAt (fun s : ℝ => scalarProfileValue a δ hδ hδ₁ (coordinateFlow 0 q s)) 0 0
      rw [heq]
      exact hasDerivAt_const _ _
    · have hev : (fun s : ℝ => scalarProfileValue a δ hδ hδ₁ (coordinateFlow 1 q s))
          =ᶠ[𝓝 0] (fun s => laminateProfileValue a δ (circleRepresentative (q 1)+s)) := by
        filter_upwards [circleRepresentative_flow_eventually hq] with s hs
        exact congrArg (laminateProfileValue a δ) hs
      have hd : HasDerivAt
          (fun s : ℝ => laminateProfileValue a δ (circleRepresentative (q 1)+s))
          (laminateProfileSlope a δ (circleRepresentative (q 1))) 0 := by
        simpa only [add_zero] using HasDerivAt.comp_const_add
          (circleRepresentative (q 1)) 0
          (laminateProfile_hasDerivAt a δ (circleRepresentative (q 1)+0))
      change HasDerivAt (fun s : ℝ => scalarProfileValue a δ hδ hδ₁ (coordinateFlow 1 q s))
        (scalarProfileSlope a δ hδ hδ₁ q) 0
      exact hd.congr_of_eventuallyEq hev

theorem scalarProfileValue_hasPartial {a δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ < 1)
    (i : Fin 2) (q : Domain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => scalarProfileValue a δ hδ hδ₁ (coordinateFlow i q s))
      (if i = 0 then 0 else scalarProfileSlope a δ hδ hδ₁ (coordinateFlow i q t)) t := by
  have h0 := scalarProfileValue_hasPartial_zero (a := a) hδ hδ₁ i (coordinateFlow i q t)
  have h0' : HasDerivAt
      (fun s : ℝ => scalarProfileValue a δ hδ hδ₁ (coordinateFlow i (coordinateFlow i q t) s))
      (if i = 0 then 0 else scalarProfileSlope a δ hδ hδ₁ (coordinateFlow i q t)) (t-t) := by
    simpa only [sub_self] using h0
  have h := h0'.comp t (h := fun s : ℝ => s-t) ((hasDerivAt_id t).sub_const t)
  convert h using 1
  · funext s
    simp only [Function.comp_apply]
    rw [HierarchicalLaminates.Fourier.coordinateFlow_add]
    congr 2
    ring
  · simp

def laminatePotential (a δ : ℝ) (hδ : 0 < δ) (hδ₁ : δ < 1)
    (z : Fin 16 → ℝ) : RegularPotential where
  potential c := z c • scalarProfileValue a δ hδ hδ₁
  gradient := ⟨fun q => WithLp.toLp 2 (fun c : Fin 2 × Fin 16 =>
      if c.1 = 0 then 0 else scalarProfileSlope a δ hδ hδ₁ q*z c.2), by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 × Fin 16 => ℝ)).comp
    apply continuous_pi
    intro c
    by_cases hc : c.1 = 0
    · simpa only [hc,ite_true] using (continuous_const : Continuous (fun _ : Domain => (0 : ℝ)))
    · simpa only [hc,ite_false] using
        (scalarProfileSlope a δ hδ hδ₁).continuous.mul_const (z c.2)⟩
  hasPartial i c q t := by
    have h := (scalarProfileValue_hasPartial (a := a) hδ hδ₁ i q t).const_mul (z c)
    convert h using 1
    by_cases hi : i = 0 <;> simp [hi]
    ring

theorem laminatePotential_gradient (a δ : ℝ) (hδ : 0 < δ) (hδ₁ : δ < 1)
    (z : Fin 16 → ℝ) (q : Domain) (i : Fin 2) (c : Fin 16) :
    (laminatePotential a δ hδ hδ₁ z).gradient q (i,c) =
      if i = 0 then 0 else scalarProfileSlope a δ hδ hδ₁ q*z c := rfl

theorem smoothTransition_derivative_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |deriv Real.smoothTransition y| ≤ C := by
  have hd : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 2)).continuous_deriv (by norm_num)
  let f : C(Icc (0 : ℝ) 1,ℝ) := ⟨fun y => deriv Real.smoothTransition y,hd.comp continuous_subtype_val⟩
  refine ⟨‖f‖,norm_nonneg _,?_⟩
  intro y
  by_cases hy : y ∈ Icc (0 : ℝ) 1
  · exact f.norm_coe_le_norm ⟨y,hy⟩
  · have hdiff : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition y) y :=
      ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)).differentiableAt.hasDerivAt
    have hzero : deriv Real.smoothTransition y = 0 := by
      rcases not_and_or.mp hy with h | h
      · have hval : Real.smoothTransition y = 0 :=
          Real.smoothTransition.zero_of_nonpos (le_of_lt (lt_of_not_ge h))
        have hm : IsLocalMin Real.smoothTransition y :=
          Filter.Eventually.of_forall (fun z => by rw [hval]; exact Real.smoothTransition.nonneg z)
        exact hm.hasDerivAt_eq_zero hdiff
      · have hval : Real.smoothTransition y = 1 :=
          Real.smoothTransition.one_of_one_le (le_of_lt (lt_of_not_ge h))
        have hm : IsLocalMax Real.smoothTransition y :=
          Filter.Eventually.of_forall (fun z => by rw [hval]; exact Real.smoothTransition.le_one z)
        exact hm.hasDerivAt_eq_zero hdiff
    simpa only [hzero,abs_zero] using norm_nonneg f

theorem rawSlabCutoffDerivative_abs_le {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (hbound : ∀ y, |deriv Real.smoothTransition y| ≤ C) (y : ℝ) :
    |rawSlabCutoffDerivative 1 δ y| ≤ 2*C/δ := by
  have hs (x : ℝ) : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition x) x :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)).differentiableAt.hasDerivAt
  have h₁ := (hs ((y-δ)/δ)).comp y (((hasDerivAt_id y).sub_const δ).div_const δ)
  have h₂ := (hs ((1-δ-y)/δ)).comp y (((hasDerivAt_id y).const_sub (1-δ)).div_const δ)
  have hd := h₁.mul h₂
  have heq : rawSlabCutoffDerivative 1 δ y =
      (deriv Real.smoothTransition ((y-δ)/δ)/δ)*Real.smoothTransition ((1-δ-y)/δ)+
      Real.smoothTransition ((y-δ)/δ)*(-deriv Real.smoothTransition ((1-δ-y)/δ)/δ) := by
    have hd' : HasDerivAt (rawSlabCutoff 1 δ)
        ((deriv Real.smoothTransition ((y-δ)/δ)/δ)*Real.smoothTransition ((1-δ-y)/δ)+
          Real.smoothTransition ((y-δ)/δ)*(-deriv Real.smoothTransition ((1-δ-y)/δ)/δ)) y := by
      convert hd using 1
      all_goals first
        | rfl
        | (simp only [Function.comp_apply,id_eq]; ring)
    exact hd'.deriv
  rw [heq]
  apply (abs_add_le _ _).trans
  have hleft : |(deriv Real.smoothTransition ((y-δ)/δ)/δ)*Real.smoothTransition ((1-δ-y)/δ)| ≤ C/δ := by
    rw [abs_mul,abs_div,abs_of_pos hδ,abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact (mul_le_mul (div_le_div_of_nonneg_right (hbound _) hδ.le)
      (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
      (div_nonneg hC hδ.le)).trans_eq (mul_one _)
  have hright : |Real.smoothTransition ((y-δ)/δ)*(-deriv Real.smoothTransition ((1-δ-y)/δ)/δ)| ≤ C/δ := by
    rw [abs_mul,abs_div,abs_neg,abs_of_pos hδ,abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact (mul_le_mul (Real.smoothTransition.le_one _)
      (div_le_div_of_nonneg_right (hbound _) hδ.le) (div_nonneg (abs_nonneg _) hδ.le)
      (by norm_num)).trans_eq (one_mul _)
  have he : C/δ+C/δ = 2*C/δ := by ring
  linarith

theorem rawLaminateSlope_abs_le {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (δ y : ℝ) :
    |rawLaminateSlope a δ y| ≤ 1 := by
  have hs := roundedCornerSlope_mem δ (y-a)
  rw [rawLaminateSlope,abs_le]
  constructor <;> linarith [ha.1,ha.2,hs.1,hs.2]

theorem laminateProfileSlope_uniform_bound {a δ C : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hδ : 0 < δ)
    (hδa : 3*δ ≤ a) (hδb : a+3*δ ≤ 1) (hC : 0 ≤ C)
    (hbound : ∀ y, |deriv Real.smoothTransition y| ≤ C)
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    |laminateProfileSlope a δ y| ≤ 4*C+1 := by
  have hp : |rawSlabCutoff 1 δ y*rawLaminateSlope a δ y| ≤ 1 := by
    rw [abs_mul,abs_of_nonneg (rawSlabCutoff_nonneg _ _ _)]
    exact (mul_le_mul (rawSlabCutoff_le_one _ _ _) (rawLaminateSlope_abs_le ha δ y)
      (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hq : |rawSlabCutoffDerivative 1 δ y*rawLaminateValue a δ y| ≤ 4*C := by
    by_cases hl : y ≤ 2*δ
    · have hv : |rawLaminateValue a δ y| ≤ 2*δ := by
        rw [rawLaminateValue_left hδ (by linarith),abs_of_nonneg
          (mul_nonneg (sub_nonneg.mpr ha.2) hy.1)]
        nlinarith [mul_nonneg ha.1 hy.1]
      rw [abs_mul]
      calc
        _ ≤ (2*C/δ)*(2*δ) := mul_le_mul
          (rawSlabCutoffDerivative_abs_le hδ hC hbound y) hv (abs_nonneg _)
          (div_nonneg (by positivity) hδ.le)
        _ = 4*C := by field_simp; ring
    · by_cases hr : 1-2*δ ≤ y
      · have hv : |rawLaminateValue a δ y| ≤ 2*δ := by
          rw [rawLaminateValue_right hδ (by linarith),abs_of_nonneg
            (mul_nonneg ha.1 (sub_nonneg.mpr hy.2))]
          nlinarith [mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hy.2)]
        rw [abs_mul]
        calc
          _ ≤ (2*C/δ)*(2*δ) := mul_le_mul
            (rawSlabCutoffDerivative_abs_le hδ hC hbound y) hv (abs_nonneg _)
            (div_nonneg (by positivity) hδ.le)
          _ = 4*C := by field_simp; ring
      · have hη : rawSlabCutoff 1 δ y = 1 :=
          rawSlabCutoff_one hδ (le_of_lt (lt_of_not_ge hl)) (le_of_lt (lt_of_not_ge hr))
        rw [rawSlabCutoffDerivative_zero_of_one hη,zero_mul,abs_zero]
        positivity
  exact (abs_add_le _ _).trans (add_le_add hq hp)

theorem scalarProfileSlope_uniform_bound {a δ C : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hδ : 0 < δ) (hδ₁ : δ < 1)
    (hδa : 3*δ ≤ a) (hδb : a+3*δ ≤ 1) (hC : 0 ≤ C)
    (hbound : ∀ y, |deriv Real.smoothTransition y| ≤ C) (q : Domain) :
    |scalarProfileSlope a δ hδ hδ₁ q| ≤ 4*C+1 :=
  laminateProfileSlope_uniform_bound ha hδ hδa hδb hC hbound
    ⟨(circleRepresentative_mem (q 1)).1,(circleRepresentative_mem (q 1)).2.le⟩

end HierarchicalLaminates.TwoWell
