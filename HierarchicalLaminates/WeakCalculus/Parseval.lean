module

public import HierarchicalLaminates.Fourier.FluxOrthogonality

/-!
# Scalar weak derivatives and Parseval

The isometric complex embedding gives Fourier coefficients for real L² fields.
Integration by parts identifies weak derivatives with angular-frequency
multipliers, and Parseval gives the mixed derivative pairing identity.
-/

@[expose] public section
noncomputable section

namespace HierarchicalLaminates.WeakCalculus

open MeasureTheory
open HierarchicalLaminates.Periodic HierarchicalLaminates.Fourier

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def complexField (u : ScalarField) : Lp ℂ 2 domainMeasure :=
  Complex.ofRealCLM.compLpL 2 domainMeasure u

theorem complexField_coe (u : ScalarField) :
    complexField u =ᵐ[domainMeasure] fun q => (u q : ℂ) :=
  Complex.ofRealCLM.coeFn_compLpL u

theorem complexField_inner (u v : ScalarField) :
    inner ℂ (complexField u) (complexField v) = (inner ℝ u v : ℂ) := by
  rw [L2.inner_def, L2.inner_def]
  trans ∫ q, (inner ℝ (u q) (v q) : ℂ) ∂domainMeasure
  · apply integral_congr_ae
    filter_upwards [complexField_coe u, complexField_coe v] with q hu hv
    rw [hu, hv]
    simp [RCLike.inner_apply]
  · exact integral_ofReal

theorem character_L2 (k : HierarchicalLaminates.Frequency) :
    UnitAddTorus.mFourierLp 2 (frequencyVector k) =
      complexField (continuousField (cosineKernel k)) +
        Complex.I • complexField (continuousField (sineKernel k)) := by
  apply Lp.ext
  filter_upwards [UnitAddTorus.coeFn_mFourierLp 2 (frequencyVector k),
    complexField_coe (continuousField (cosineKernel k)),
    complexField_coe (continuousField (sineKernel k)),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure (cosineKernel k),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure (sineKernel k),
    Lp.coeFn_add (complexField (continuousField (cosineKernel k)))
      (Complex.I • complexField (continuousField (sineKernel k))),
    Lp.coeFn_smul Complex.I (complexField (continuousField (sineKernel k)))]
    with q hchar hcos hsin hcos' hsin' hadd hsmul
  simp only [Pi.add_apply, Pi.smul_apply] at hadd hsmul
  erw [hadd, hsmul, hcos, hsin, hcos', hsin', hchar]
  change phaseCharacter k q = _
  simpa [cosineKernel, sineKernel, smul_eq_mul, mul_comm] using
    (Complex.re_add_im (phaseCharacter k q)).symm

theorem coefficient_complexField (u : ScalarField) (k : HierarchicalLaminates.Frequency) :
    UnitAddTorus.mFourierCoeff (complexField u) (frequencyVector k) =
      (inner ℝ u (continuousField (cosineKernel k)) : ℂ) -
        Complex.I * (inner ℝ u (continuousField (sineKernel k)) : ℂ) := by
  erw [← UnitAddTorus.mFourierBasis_repr,
    HilbertBasis.repr_apply_apply, UnitAddTorus.coe_mFourierBasis,
    character_L2, inner_add_left, inner_smul_left,
    complexField_inner, complexField_inner]
  simp only [Complex.conj_I]
  rw [real_inner_comm (continuousField (cosineKernel k)) u,
    real_inner_comm (continuousField (sineKernel k)) u]
  ring

def HasWeakPartial (u du : ScalarField) (i : Fin 2) : Prop :=
  ∀ test : SmoothTest,
    inner ℝ du (continuousField test.value) =
      -inner ℝ u (continuousField (test.derivative i))

theorem HasWeakPartial.coefficient {u du : ScalarField} {i : Fin 2}
    (hu : HasWeakPartial u du i) (k : HierarchicalLaminates.Frequency) :
    UnitAddTorus.mFourierCoeff (complexField du) (frequencyVector k) =
      (angularFrequency k i : ℂ) * Complex.I *
        UnitAddTorus.mFourierCoeff (complexField u) (frequencyVector k) := by
  have hcos := hu (cosineTest k)
  have hsin := hu (sineTest k)
  simp only [cosineTest, sineTest, map_smul, inner_smul_right, neg_mul, neg_neg] at hcos hsin
  rw [coefficient_complexField, coefficient_complexField, hcos, hsin]
  unfold angularFrequency
  push_cast
  ring_nf
  simp [Complex.I_sq]

theorem hasSum_coefficients_inner (u v : ScalarField) :
    HasSum (fun k : Fin 2 → ℤ =>
      starRingEnd ℂ (UnitAddTorus.mFourierCoeff (complexField u) k) *
        UnitAddTorus.mFourierCoeff (complexField v) k)
      (inner ℝ u v : ℂ) := by
  have h := UnitAddTorus.hasSum_prod_mFourierCoeff (complexField u) (complexField v)
  change HasSum _ (∫ q, starRingEnd ℂ (complexField u q) * complexField v q
    ∂domainMeasure) at h
  have hp : (∫ q, starRingEnd ℂ (complexField u q) * complexField v q
      ∂domainMeasure) = inner ℂ (complexField u) (complexField v) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun q => by
      simp only [RCLike.inner_apply]
      ring)
  rw [hp, complexField_inner] at h
  exact h

/-- The mixed derivative pairing identity for L² potentials with L² weak derivatives. -/
theorem mixed_pairing {u v ux uy vx vy : ScalarField}
    (hux : HasWeakPartial u ux 0) (huy : HasWeakPartial u uy 1)
    (hvx : HasWeakPartial v vx 0) (hvy : HasWeakPartial v vy 1) :
    inner ℝ ux vy = inner ℝ uy vx := by
  have hterms : ∀ k : Fin 2 → ℤ,
      starRingEnd ℂ (UnitAddTorus.mFourierCoeff (complexField ux) k) *
          UnitAddTorus.mFourierCoeff (complexField vy) k =
        starRingEnd ℂ (UnitAddTorus.mFourierCoeff (complexField uy) k) *
          UnitAddTorus.mFourierCoeff (complexField vx) k := by
    intro k
    have hk : frequencyVector (k 0, k 1) = k := by
      ext i
      fin_cases i <;> rfl
    rw [← hk, hux.coefficient, huy.coefficient, hvx.coefficient, hvy.coefficient]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  apply Complex.ofReal_injective
  exact (hasSum_coefficients_inner ux vy).unique
    ((hasSum_coefficients_inner uy vx).congr_fun (fun k => hterms k))

end HierarchicalLaminates.WeakCalculus
