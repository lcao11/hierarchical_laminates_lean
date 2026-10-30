module

public import HierarchicalLaminates.Material.ScalarMultiplication
public import HierarchicalLaminates.Fourier.IntegrationByParts
public import HierarchicalLaminates.Fourier.Differentiation

/-!
# Weak multiplication by differentiable Fourier synthesis

Absolute summability of the value and derivative coefficients permits summing
the smooth mode product identities in L².
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Corrector

open MeasureTheory HierarchicalLaminates.Periodic HierarchicalLaminates.Material HierarchicalLaminates.Fourier

/-- The scalar weak partial derivative defined by integration by parts. -/
def ScalarWeakPartial (u du : ScalarField) (i : Fin 2) : Prop :=
  ∀ test : SmoothTest, inner ℝ du (continuousField test.value) =
    -inner ℝ u (continuousField (test.derivative i))

def continuousBounded (s : C(Domain, ℝ)) : BoundedScalar where
  value := s
  measurable := s.continuous.measurable
  bound := ‖s‖
  bound_nonneg := norm_nonneg _
  abs_le := fun q => by simpa only [Real.norm_eq_abs] using s.norm_coe_le_norm q

def continuousProduct (s : C(Domain, ℝ)) (u : ScalarField) : ScalarField :=
  scalarMultiplication (continuousBounded s) u

lemma continuousProduct_coe (s : C(Domain, ℝ)) (u : ScalarField) :
    continuousProduct s u =ᵐ[domainMeasure] fun q => s q * u q :=
  scalarMultiplication_coe _ _

lemma continuousProduct_norm_le (s : C(Domain, ℝ)) (u : ScalarField) :
    ‖continuousProduct s u‖ ≤ ‖s‖ * ‖u‖ := by
  change ‖scalarProduct (continuousBounded s) u‖ ≤ _
  exact scalarProduct_norm_le (continuousBounded s) u

lemma continuousProduct_add_right (s : C(Domain, ℝ)) (u v : ScalarField) :
    continuousProduct s (u + v) = continuousProduct s u + continuousProduct s v :=
  (scalarMultiplication (continuousBounded s)).map_add u v

lemma continuousProduct_add_left (s t : C(Domain, ℝ)) (u : ScalarField) :
    continuousProduct (s + t) u = continuousProduct s u + continuousProduct t u := by
  apply Lp.ext
  filter_upwards [continuousProduct_coe (s + t) u, continuousProduct_coe s u,
    continuousProduct_coe t u, Lp.coeFn_add (continuousProduct s u) (continuousProduct t u)]
    with q hst hs ht hadd
  simp only [hst, hadd, hs, ht, Pi.add_apply, ContinuousMap.add_apply, add_mul]

lemma continuousProduct_smul_left (c : ℝ) (s : C(Domain, ℝ)) (u : ScalarField) :
    continuousProduct (c • s) u = c • continuousProduct s u := by
  apply Lp.ext
  filter_upwards [continuousProduct_coe (c • s) u, continuousProduct_coe s u,
    Lp.coeFn_smul c (continuousProduct s u)] with q hc hs hout
  simp only [hc, hs, hout, ContinuousMap.smul_apply, Pi.smul_apply, smul_eq_mul,
    mul_assoc]

def continuousMultiplicationLinear (u : ScalarField) : C(Domain, ℝ) →ₗ[ℝ] ScalarField where
  toFun s := continuousProduct s u
  map_add' s t := continuousProduct_add_left s t u
  map_smul' c s := continuousProduct_smul_left c s u

def continuousMultiplication (u : ScalarField) : C(Domain, ℝ) →L[ℝ] ScalarField :=
  (continuousMultiplicationLinear u).mkContinuous ‖u‖ (fun s => by
    change ‖scalarProduct (continuousBounded s) u‖ ≤ ‖u‖ * ‖s‖
    simpa only [continuousBounded, mul_comm] using scalarProduct_norm_le (continuousBounded s) u)

lemma continuousProduct_continuousField (s t : C(Domain, ℝ)) :
    continuousProduct s (continuousField t) = continuousField (s * t) := by
  apply Lp.ext
  filter_upwards [continuousProduct_coe s (continuousField t),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure t,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure (s * t)] with q hp ht hst
  change continuousField t q = t q at ht
  change continuousField (s * t) q = (s * t) q at hst
  rw [hp, ht, hst]
  rfl

lemma continuousProduct_pairing (s t : C(Domain, ℝ)) (u : ScalarField) :
    inner ℝ (continuousProduct s u) (continuousField t) =
      inner ℝ u (continuousField (s * t)) := by
  rw [continuousProduct, scalarMultiplication_symmetric]
  rw [← continuousProduct, continuousProduct_continuousField]

def testProduct (s t : SmoothTest) : SmoothTest where
  value := s.value * t.value
  derivative i := s.derivative i * t.value + s.value * t.derivative i
  smooth := s.smooth.mul t.smooth
  hasPartial i q := by
    convert (s.hasPartial i q).mul (t.hasPartial i q) using 1
    simp only [coordinateFlow_zero, ContinuousMap.mul_apply, ContinuousMap.add_apply]

def testScale (c : ℝ) (s : SmoothTest) : SmoothTest where
  value := c • s.value
  derivative i := c • s.derivative i
  smooth := s.smooth.const_smul c
  hasPartial i q := (s.hasPartial i q).const_smul c

lemma ScalarWeakPartial.product_test {u du : ScalarField} {i : Fin 2}
    (hu : ScalarWeakPartial u du i) (s : SmoothTest) :
    ScalarWeakPartial (continuousProduct s.value u)
      (continuousProduct s.value du + continuousProduct (s.derivative i) u) i := by
  intro test
  have h := hu (testProduct s test)
  change inner ℝ du (continuousField (s.value * test.value)) =
    -inner ℝ u (continuousField (s.derivative i * test.value + s.value * test.derivative i)) at h
  rw [map_add, inner_add_right] at h
  rw [inner_add_left, continuousProduct_pairing, continuousProduct_pairing,
    continuousProduct_pairing]
  linarith

lemma ScalarWeakPartial.tsum {ι : Type*} {u du : ι → ScalarField} {i : Fin 2}
    (hu : Summable u) (hdu : Summable du) (h : ∀ k, ScalarWeakPartial (u k) (du k) i) :
    ScalarWeakPartial (∑' k, u k) (∑' k, du k) i := by
  intro test
  have h₁ := ((innerSL ℝ).flip (continuousField test.value)).map_tsum hdu
  have h₂ := ((innerSL ℝ).flip (continuousField (test.derivative i))).map_tsum hu
  change inner ℝ (∑' k, du k) (continuousField test.value) =
    ∑' k, inner ℝ (du k) (continuousField test.value) at h₁
  change inner ℝ (∑' k, u k) (continuousField (test.derivative i)) =
    ∑' k, inner ℝ (u k) (continuousField (test.derivative i)) at h₂
  rw [h₁, h₂]
  calc
    (∑' k, inner ℝ (du k) (continuousField test.value)) =
        ∑' k, -inner ℝ (u k) (continuousField (test.derivative i)) := tsum_congr (fun k => h k test)
    _ = _ := tsum_neg

lemma weakProduct_cosineSynthesis {u du : ScalarField} {i : Fin 2}
    (hu : ScalarWeakPartial u du i)
    (f g : Coefficients HierarchicalLaminates.Frequency ℝ)
    (hg : ∀ k, g k = -(angularFrequency k i) * f k) :
    ScalarWeakPartial (continuousProduct (cosineSynthesis f) u)
      (continuousProduct (cosineSynthesis f) du + continuousProduct (sineSynthesis g) u) i := by
  let U k := continuousMultiplication u (synthesisTerm cosineKernel f k)
  let D₁ k := continuousMultiplication du (synthesisTerm cosineKernel f k)
  let D₂ k := continuousMultiplication u (synthesisTerm sineKernel g k)
  have hU : Summable U := (continuousMultiplication u).summable
    (synthesisTerm_summable cosineKernel cosineKernel_norm_le f)
  have hD₁ : Summable D₁ := (continuousMultiplication du).summable
    (synthesisTerm_summable cosineKernel cosineKernel_norm_le f)
  have hD₂ : Summable D₂ := (continuousMultiplication u).summable
    (synthesisTerm_summable sineKernel sineKernel_norm_le g)
  have hmode (k) : ScalarWeakPartial (U k) (D₁ k + D₂ k) i := by
    have h := hu.product_test (testScale (f k) (cosineTest k))
    have hv : synthesisTerm cosineKernel f k = (testScale (f k) (cosineTest k)).value := by
      ext q
      simp [testScale, cosineTest, synthesisTerm, mul_comm]
    have hd : synthesisTerm sineKernel g k = (testScale (f k) (cosineTest k)).derivative i := by
      ext q
      simp [testScale, cosineTest, synthesisTerm, hg, angularFrequency]
      ring
    change ScalarWeakPartial (continuousProduct (synthesisTerm cosineKernel f k) u)
      (continuousProduct (synthesisTerm cosineKernel f k) du +
        continuousProduct (synthesisTerm sineKernel g k) u) i
    rw [hv, hd]
    exact h
  have h := ScalarWeakPartial.tsum hU (hD₁.add hD₂) hmode
  dsimp only [U, D₁, D₂] at h
  rw [hD₁.tsum_add hD₂] at h
  rw [← (continuousMultiplication u).map_tsum
      (synthesisTerm_summable cosineKernel cosineKernel_norm_le f),
    ← (continuousMultiplication du).map_tsum
      (synthesisTerm_summable cosineKernel cosineKernel_norm_le f),
    ← (continuousMultiplication u).map_tsum
      (synthesisTerm_summable sineKernel sineKernel_norm_le g)] at h
  exact h

end HierarchicalLaminates.Corrector
