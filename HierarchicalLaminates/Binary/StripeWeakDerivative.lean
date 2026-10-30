module

public import HierarchicalLaminates.Binary.HeightIntegral
public import HierarchicalLaminates.Fourier.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Weak derivative of the stripe primitive

For each horizontal coordinate, the interface is a singleton and has measure
zero. Integration by parts includes the kink and both strip endpoints.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Binary

open MeasureTheory Set HierarchicalLaminates.Periodic HierarchicalLaminates.Fourier

/-- A minimum of affine functions is absolutely continuous, despite its kink. -/
theorem stripePrimitive_absolutelyContinuous (h t a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun τ => stripePrimitive h τ t) a b := by
  have hmin : AbsolutelyContinuousOnInterval (fun τ : ℝ => min τ t) a b :=
    (LipschitzWith.id.min_const t).lipschitzOnWith.absolutelyContinuousOnInterval
  have hlinear : AbsolutelyContinuousOnInterval (fun τ : ℝ => τ * t) a b :=
    (contDiff_id.mul contDiff_const).contDiffOn.absolutelyContinuousOnInterval
  exact (hmin.fun_sub hlinear).const_mul h

/-- The classical derivative formula holds almost everywhere, including at endpoint widths. -/
theorem stripePrimitive_ae_deriv (h t : ℝ) :
    deriv (fun τ => stripePrimitive h τ t) =ᵐ[volume]
      (fun τ => h * (stripeIndicator τ t - t)) := by
  filter_upwards [volume.ae_ne t] with τ hτ
  exact (primitive_derivative h τ t hτ).deriv

/-- Weak differentiation has no interface delta term because the primitive is continuous. -/
theorem stripePrimitive_integrationByParts {h t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {φ φ' : ℝ → ℝ} (hφ : AbsolutelyContinuousOnInterval φ 0 1)
    (hφ' : ∀ τ : ℝ, HasDerivAt φ (φ' τ) τ) :
    (∫ τ in (0 : ℝ)..1, stripePrimitive h τ t * φ' τ) =
      -(∫ τ in (0 : ℝ)..1, h * (stripeIndicator τ t - t) * φ τ) := by
  have hIBP := (stripePrimitive_absolutelyContinuous h t 0 1).integral_mul_deriv_eq_deriv_mul hφ
  have hleft : (∫ τ in (0 : ℝ)..1, stripePrimitive h τ t * deriv φ τ) =
      ∫ τ in (0 : ℝ)..1, stripePrimitive h τ t * φ' τ := by
    apply intervalIntegral.integral_congr
    intro τ hτ
    dsimp only
    rw [(hφ' τ).deriv]
  have hright : (∫ τ in (0 : ℝ)..1, deriv (fun s => stripePrimitive h s t) τ * φ τ) =
      ∫ τ in (0 : ℝ)..1, h * (stripeIndicator τ t - t) * φ τ := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [stripePrimitive_ae_deriv h t] with τ hτ hmem
    rw [hτ]
  rw [hleft, hright, primitive_at_one (h := h) ht.2, primitive_at_zero (h := h) ht.1] at hIBP
  simpa using hIBP

theorem vertical_coordinateFlow (x : UnitAddCircle) (s : ℝ) :
    coordinateFlow 1 ![x, (0 : UnitAddCircle)] s = ![x, (s : UnitAddCircle)] := by
  ext i
  fin_cases i <;> simp [coordinateFlow]

theorem smoothTest_hasDerivAt_pointInStrip (test : SmoothTest) (N k : ℕ)
    (x : UnitAddCircle) (τ : ℝ) :
    HasDerivAt (fun s : ℝ => test.value (pointInStrip N k x s))
      ((1 / (N : ℝ)) * test.derivative 1 (pointInStrip N k x τ)) τ := by
  have htest := smoothTest_hasDerivAt_flow test 1 ![x, (0 : UnitAddCircle)]
    (((k : ℝ) + τ) / N)
  have harg : HasDerivAt (fun s : ℝ => ((k : ℝ) + s) / N) (1 / (N : ℝ)) τ := by
    exact ((hasDerivAt_id τ).const_add (k : ℝ)).div_const (N : ℝ)
  have hcomp := htest.comp τ harg
  simp_rw [vertical_coordinateFlow] at hcomp
  convert hcomp using 1 <;> first | rfl | simp only [pointInStrip, mul_comm]

theorem smoothTest_pointInStrip_contDiff (test : SmoothTest) (N k : ℕ)
    (x : UnitAddCircle) :
    ContDiff ℝ 1 (fun τ : ℝ => test.value (pointInStrip N k x τ)) := by
  let xr : ℝ := (AddCircle.equivIco 1 0 x).1
  have hxr : (xr : UnitAddCircle) = x := AddCircle.coe_equivIco
  have hmap : ContDiff ℝ 1 (fun τ : ℝ => ![xr, ((k : ℝ) + τ) / N]) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact contDiff_const
    · exact (contDiff_const.add contDiff_id).div_const (N : ℝ)
  have hsmooth : ContDiff ℝ 1 (realLift test.value) := test.smooth.of_le (by simp)
  have ht := hsmooth.comp hmap
  convert ht using 1
  funext τ
  unfold realLift pointInStrip
  congr 1
  ext i
  fin_cases i
  · exact hxr.symm
  · rfl

/-- A smooth torus test is an admissible absolutely continuous test on every stripe. -/
theorem smoothTest_pointInStrip_absolutelyContinuous (test : SmoothTest) (N k : ℕ)
    (x : UnitAddCircle) :
    AbsolutelyContinuousOnInterval (fun τ : ℝ => test.value (pointInStrip N k x τ)) 0 1 :=
  (smoothTest_pointInStrip_contDiff test N k x).contDiffOn.absolutelyContinuousOnInterval

/-- Vertical weak differentiation in local coordinates against smooth torus tests. -/
theorem stripePrimitive_test_vertical_integrationByParts {N k : ℕ} (hN : 0 < N)
    (test : SmoothTest) (x : UnitAddCircle) :
    (∫ τ in (0 : ℝ)..1, stripePrimitive (1 / (N : ℝ)) τ (stripFraction N k x) *
      test.derivative 1 (pointInStrip N k x τ)) =
      -(∫ τ in (0 : ℝ)..1, (stripeIndicator τ (stripFraction N k x) - stripFraction N k x) *
        test.value (pointInStrip N k x τ)) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have h := stripePrimitive_integrationByParts
    (h := 1 / (N : ℝ))
    (show stripFraction N k x ∈ Icc (0 : ℝ) 1 from
      ⟨cosineProfile_nonneg _, cosineProfile_le_one _⟩)
    (smoothTest_pointInStrip_absolutelyContinuous test N k x)
    (smoothTest_hasDerivAt_pointInStrip test N k x)
  have hleft : (fun τ : ℝ => stripePrimitive (1 / (N : ℝ)) τ (stripFraction N k x) *
      ((1 / (N : ℝ)) * test.derivative 1 (pointInStrip N k x τ))) =
      (fun τ : ℝ => (1 / (N : ℝ)) * (stripePrimitive (1 / (N : ℝ)) τ (stripFraction N k x) *
      test.derivative 1 (pointInStrip N k x τ))) := by
    funext τ
    ring
  have hright : (fun τ : ℝ => (1 / (N : ℝ)) *
      (stripeIndicator τ (stripFraction N k x) - stripFraction N k x) *
      test.value (pointInStrip N k x τ)) =
      (fun τ : ℝ => (1 / (N : ℝ)) *
        ((stripeIndicator τ (stripFraction N k x) - stripFraction N k x) *
        test.value (pointInStrip N k x τ))) := by
    funext τ
    ring
  rw [hleft, hright, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, ← mul_neg] at h
  exact mul_left_cancel₀ (one_div_ne_zero hNr) h

end HierarchicalLaminates.Binary
