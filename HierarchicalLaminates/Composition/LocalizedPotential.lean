module

public import HierarchicalLaminates.Composition.LocalizedPotentialLift

/-!
# Localizing a microscopic periodic potential
-/

@[expose] public section
noncomputable section

namespace HierarchicalLaminates.Composition

open HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Binary HierarchicalLaminates.Homogenization
open Set Filter
open scoped Topology

def microSlabCoordinates (a : ℝ) (r k : ℕ) (x : UnitAddCircle) (y : ℝ) : Domain :=
  ![r • x, (((k : ℝ) / a * y : ℝ) : UnitAddCircle)]

theorem microSlabCoordinates_continuous (a : ℝ) (r k : ℕ) :
    Continuous (fun p : UnitAddCircle × ℝ => microSlabCoordinates a r k p.1 p.2) := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact (continuous_nsmul r).comp continuous_fst
  · exact (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_const.mul continuous_snd)

theorem microSlabCoordinates_horizontal (a : ℝ) (r k : ℕ)
    (x : UnitAddCircle) (y s : ℝ) :
    microSlabCoordinates a r k (x + (s : UnitAddCircle)) y =
      coordinateFlow 0 (microSlabCoordinates a r k x y) ((r : ℝ) * s) := by
  ext i
  fin_cases i
  · simp only [microSlabCoordinates, coordinateFlow, Pi.add_apply, nsmul_add]
    rw [← AddCircle.coe_nsmul]
    simp [nsmul_eq_mul]
  · simp [microSlabCoordinates, coordinateFlow]

theorem microSlabCoordinates_vertical (a : ℝ) (r k : ℕ)
    (x : UnitAddCircle) (y s : ℝ) :
    microSlabCoordinates a r k x (y + s) =
      coordinateFlow 1 (microSlabCoordinates a r k x y) ((k : ℝ) / a * s) := by
  ext i
  fin_cases i
  · simp [microSlabCoordinates, coordinateFlow]
  · change (((k : ℝ) / a * (y + s) : ℝ) : UnitAddCircle) =
      (((k : ℝ) / a * y : ℝ) : UnitAddCircle) +
        (((k : ℝ) / a * s : ℝ) : UnitAddCircle)
    rw [mul_add, AddCircle.coe_add]

theorem microSlabCoordinates_eq_recoveryCoordinates (a : ℝ) (r k : ℕ) (q : Domain) :
    microSlabCoordinates a r k (q 0) (circleRepresentative (q 1)) =
      recoveryCoordinates a r k q := by
  ext i
  fin_cases i
  · rfl
  · change (((k : ℝ) / a * circleRepresentative (q 1) : ℝ) : UnitAddCircle) =
      k • ((coordinateRepresentative 1 q / a : ℝ) : UnitAddCircle)
    rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
    congr 1
    rw [coordinateRepresentative_eq_circleRepresentative]
    ring

def localizedRawValue (a δ : ℝ) (r k : ℕ) (u : RegularPotential) (c : Fin 16)
    (x : UnitAddCircle) (y : ℝ) : ℝ :=
  (r : ℝ)⁻¹ * rawSlabCutoff a δ y * u.potential c (microSlabCoordinates a r k x y)

def localizedRawGradient (a δ : ℝ) (r k : ℕ) (u : RegularPotential)
    (x : UnitAddCircle) (y : ℝ) : PhysicalGradient :=
  WithLp.toLp 2 (fun p => if p.1 = 0 then
    rawSlabCutoff a δ y * u.gradient (microSlabCoordinates a r k x y) (0, p.2)
  else
    ((k : ℝ) / (a * r)) * rawSlabCutoff a δ y *
      u.gradient (microSlabCoordinates a r k x y) (1, p.2) +
    (r : ℝ)⁻¹ * rawSlabCutoffDerivative a δ y *
      u.potential p.2 (microSlabCoordinates a r k x y))

theorem localizedRawValue_continuous (a δ : ℝ) (r k : ℕ) (u : RegularPotential)
    (c : Fin 16) : Continuous (Function.uncurry (localizedRawValue a δ r k u c)) := by
  exact (continuous_const.mul ((rawSlabCutoff_contDiff a δ).continuous.comp continuous_snd)).mul
    ((u.potential c).continuous.comp (microSlabCoordinates_continuous a r k))

theorem localizedRawGradient_continuous (a δ : ℝ) (r k : ℕ) (u : RegularPotential) :
    Continuous (Function.uncurry (localizedRawGradient a δ r k u)) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 × Fin 16 => ℝ)).comp
  apply continuous_pi
  intro p
  dsimp [localizedRawGradient]
  split_ifs with hp
  · exact ((rawSlabCutoff_contDiff a δ).continuous.comp continuous_snd).mul
      (((EuclideanSpace.proj (𝕜 := ℝ) (0, p.2)).continuous.comp u.gradient.continuous).comp
        (microSlabCoordinates_continuous a r k))
  · exact ((continuous_const.mul
      ((rawSlabCutoff_contDiff a δ).continuous.comp continuous_snd)).mul
      (((EuclideanSpace.proj (𝕜 := ℝ) (1, p.2)).continuous.comp u.gradient.continuous).comp
        (microSlabCoordinates_continuous a r k))).add
      ((continuous_const.mul ((rawSlabCutoffDerivative_continuous a δ).comp continuous_snd)).mul
        ((u.potential p.2).continuous.comp (microSlabCoordinates_continuous a r k)))

theorem localizedRawValue_zero {a δ : ℝ} (hδ : 0 < δ) (r k : ℕ)
    (u : RegularPotential) (c : Fin 16) (x : UnitAddCircle) (y : ℝ)
    (hy : y ∉ Icc δ (a - δ)) : localizedRawValue a δ r k u c x y = 0 := by
  have hz : rawSlabCutoff a δ y = 0 := by
    rcases (not_and_or.mp hy) with h | h
    · exact rawSlabCutoff_zero_left a hδ (by linarith)
    · exact rawSlabCutoff_zero_right hδ (by linarith)
  simp [localizedRawValue, hz]

theorem localizedRawGradient_zero {a δ : ℝ} (hδ : 0 < δ) (r k : ℕ)
    (u : RegularPotential) (x : UnitAddCircle) (y : ℝ)
    (hy : y ∉ Icc δ (a - δ)) : localizedRawGradient a δ r k u x y = 0 := by
  have hz : rawSlabCutoff a δ y = 0 := by
    rcases (not_and_or.mp hy) with h | h
    · exact rawSlabCutoff_zero_left a hδ (by linarith)
    · exact rawSlabCutoff_zero_right hδ (by linarith)
  have hdz := rawSlabCutoffDerivative_zero_of_zero hz
  ext p
  simp [localizedRawGradient, hz, hdz]

def localizedPotentialValue (a δ : ℝ) (ha : a ≤ 1) (hδ : 0 < δ)
    (r k : ℕ) (u : RegularPotential) (c : Fin 16) : C(Domain, ℝ) :=
  ⟨liftSlabFamily (localizedRawValue a δ r k u c),
    liftSlabFamily_continuous hδ (by linarith)
      (localizedRawValue_continuous a δ r k u c)
      (localizedRawValue_zero hδ r k u c)⟩

def localizedPotentialGradient (a δ : ℝ) (ha : a ≤ 1) (hδ : 0 < δ)
    (r k : ℕ) (u : RegularPotential) : C(Domain, PhysicalGradient) :=
  ⟨liftSlabFamily (localizedRawGradient a δ r k u),
    liftSlabFamily_continuous hδ (by linarith)
      (localizedRawGradient_continuous a δ r k u)
      (localizedRawGradient_zero hδ r k u)⟩

theorem localizedRawValue_hasDerivAt_horizontal (a δ : ℝ) {r : ℕ} (hr : 0 < r)
    (k : ℕ) (u : RegularPotential) (c : Fin 16) (x : UnitAddCircle) (y : ℝ) :
    HasDerivAt (fun s : ℝ => localizedRawValue a δ r k u c (x + (s : UnitAddCircle)) y)
      (localizedRawGradient a δ r k u x y (0, c)) 0 := by
  have hrne : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hu := (u.hasPartial 0 c (microSlabCoordinates a r k x y) ((r : ℝ) * 0)).comp 0
    ((hasDerivAt_id (0 : ℝ)).const_mul (r : ℝ))
  have hu' : HasDerivAt
      (fun s : ℝ => u.potential c (microSlabCoordinates a r k (x + (s : UnitAddCircle)) y))
      (u.gradient (microSlabCoordinates a r k x y) (0, c) * r) 0 := by
    convert hu using 1
    · ext s
      exact congrArg (u.potential c) (microSlabCoordinates_horizontal a r k x y s)
    · simp [HierarchicalLaminates.Fourier.coordinateFlow_zero]
  convert hu'.const_mul ((r : ℝ)⁻¹ * rawSlabCutoff a δ y) using 1
  · rfl
  · change rawSlabCutoff a δ y * u.gradient (microSlabCoordinates a r k x y) (0, c) = _
    field_simp

theorem localizedRawValue_hasDerivAt_vertical {a : ℝ} (ha : a ≠ 0) (δ : ℝ)
    {r : ℕ} (hr : 0 < r) (k : ℕ) (u : RegularPotential) (c : Fin 16)
    (x : UnitAddCircle) (y : ℝ) :
    HasDerivAt (fun s : ℝ => localizedRawValue a δ r k u c x (y + s))
      (localizedRawGradient a δ r k u x y (1, c)) 0 := by
  have hrne : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hu := (u.hasPartial 1 c (microSlabCoordinates a r k x y) (((k : ℝ) / a) * 0)).comp 0
    ((hasDerivAt_id (0 : ℝ)).const_mul ((k : ℝ) / a))
  have hu' : HasDerivAt
      (fun s : ℝ => u.potential c (microSlabCoordinates a r k x (y + s)))
      (u.gradient (microSlabCoordinates a r k x y) (1, c) * ((k : ℝ) / a)) 0 := by
    convert hu using 1
    · ext s
      exact congrArg (u.potential c) (microSlabCoordinates_vertical a r k x y s)
    · simp [HierarchicalLaminates.Fourier.coordinateFlow_zero]
  have hη : HasDerivAt (fun s : ℝ => rawSlabCutoff a δ (y + s))
      (rawSlabCutoffDerivative a δ y) 0 := by
    simpa only [add_zero] using HasDerivAt.comp_const_add y 0
      (rawSlabCutoff_hasDerivAt a δ (y + 0))
  convert (hη.const_mul (r : ℝ)⁻¹).mul hu' using 1
  · rfl
  · change ((k : ℝ) / (a * r)) * rawSlabCutoff a δ y *
        u.gradient (microSlabCoordinates a r k x y) (1, c) +
        (r : ℝ)⁻¹ * rawSlabCutoffDerivative a δ y *
        u.potential c (microSlabCoordinates a r k x y) = _
    simp only [add_zero]
    field_simp
    ring

theorem localizedPotential_hasPartial_zero {a δ : ℝ} (ha₀ : 0 < a) (ha : a ≤ 1)
    (hδ : 0 < δ) {r : ℕ} (hr : 0 < r) (k : ℕ) (u : RegularPotential)
    (i : Fin 2) (c : Fin 16) (q : Domain) :
    HasDerivAt
      (fun s : ℝ => localizedPotentialValue a δ ha hδ r k u c (coordinateFlow i q s))
      (localizedPotentialGradient a δ ha hδ r k u q (i, c)) 0 := by
  by_cases hq : q 1 = 0
  · have hev : (fun s : ℝ => localizedPotentialValue a δ ha hδ r k u c
        (coordinateFlow i q s)) =ᶠ[𝓝 0] (fun _ => 0) := by
      have ht : Tendsto (coordinateFlow i q) (𝓝 (0 : ℝ)) (𝓝 q) := by
        have hc : Continuous (coordinateFlow i q) := by
          exact continuous_const.add ((continuous_single i).comp (AddCircle.continuous_mk' (1 : ℝ)))
        have ht : Tendsto (coordinateFlow i q) (𝓝 (0 : ℝ)) (𝓝 (coordinateFlow i q 0)) :=
          hc.continuousAt
        simpa only [HierarchicalLaminates.Fourier.coordinateFlow_zero] using ht
      exact ht.eventually (liftSlabFamily_eventually_zero hδ (by linarith)
        (localizedRawValue_zero hδ r k u c) hq)
    have hg : localizedPotentialGradient a δ ha hδ r k u q = 0 := by
      apply localizedRawGradient_zero hδ
      rw [hq, circleRepresentative_zero]
      exact fun h => (not_le.mpr hδ) h.1
    rw [hg]
    exact (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hev
  · fin_cases i
    · convert localizedRawValue_hasDerivAt_horizontal a δ hr k u c (q 0)
        (circleRepresentative (q 1)) using 1
      · ext s
        simp [localizedPotentialValue, liftSlabFamily, coordinateFlow_eval]
      · rfl
    · have hev : (fun s : ℝ => localizedPotentialValue a δ ha hδ r k u c
          (coordinateFlow 1 q s)) =ᶠ[𝓝 0]
          (fun s => localizedRawValue a δ r k u c (q 0) (circleRepresentative (q 1) + s)) := by
        filter_upwards [circleRepresentative_flow_eventually hq] with s hs
        simp only [localizedPotentialValue, ContinuousMap.coe_mk, liftSlabFamily, hs]
        congr 2
        simp [coordinateFlow_eval]
      exact (localizedRawValue_hasDerivAt_vertical ha₀.ne' δ hr k u c (q 0)
        (circleRepresentative (q 1))).congr_of_eventuallyEq hev

theorem localizedPotential_hasPartial {a δ : ℝ} (ha₀ : 0 < a) (ha : a ≤ 1)
    (hδ : 0 < δ) {r : ℕ} (hr : 0 < r) (k : ℕ) (u : RegularPotential)
    (i : Fin 2) (c : Fin 16) (q : Domain) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => localizedPotentialValue a δ ha hδ r k u c (coordinateFlow i q s))
      (localizedPotentialGradient a δ ha hδ r k u (coordinateFlow i q t) (i, c)) t := by
  have h0 := localizedPotential_hasPartial_zero ha₀ ha hδ hr k u i c (coordinateFlow i q t)
  have h0' : HasDerivAt
      (fun s : ℝ => localizedPotentialValue a δ ha hδ r k u c
        (coordinateFlow i (coordinateFlow i q t) s))
      (localizedPotentialGradient a δ ha hδ r k u (coordinateFlow i q t) (i, c)) (t - t) := by
    simpa only [sub_self] using h0
  have h := h0'.comp t (h := fun s : ℝ => s - t) ((hasDerivAt_id t).sub_const t)
  convert h using 1
  · ext s
    simp only [Function.comp_apply]
    rw [HierarchicalLaminates.Fourier.coordinateFlow_add]
    congr 2
    ring
  · simp

def localizedPotential {a δ : ℝ} (ha₀ : 0 < a) (ha : a ≤ 1) (hδ : 0 < δ)
    {r : ℕ} (hr : 0 < r) (k : ℕ) (u : RegularPotential) : RegularPotential where
  potential := localizedPotentialValue a δ ha hδ r k u
  gradient := localizedPotentialGradient a δ ha hδ r k u
  hasPartial := localizedPotential_hasPartial ha₀ ha hδ hr k u

end HierarchicalLaminates.Composition
