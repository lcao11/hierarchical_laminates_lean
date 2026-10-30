module

public import HierarchicalLaminates.Composition.MacroPrimitive

/-! The exact equilibrated flux of arithmetic horizontal layers. -/

@[expose] public section
noncomputable section

namespace HierarchicalLaminates.Composition

open MeasureTheory Set HierarchicalLaminates.Homogenization HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Binary
open HierarchicalLaminates.Fourier HierarchicalLaminates.WeakCalculus

def spanField (v : PhysicalGradient) (f : ScalarField) : PhysicalField :=
  (ContinuousLinearMap.toSpanSingleton ℝ v).compLpL 2 domainMeasure f

theorem spanField_coe (v : PhysicalGradient) (f : ScalarField) :
    spanField v f =ᵐ[domainMeasure] fun q => f q • v :=
  (ContinuousLinearMap.toSpanSingleton ℝ v).coeFn_compLpL f

theorem componentField_spanField (v : PhysicalGradient) (f : ScalarField)
    (i : Fin 2) (a : Fin 16) :
    componentField i a (spanField v f) = v (i,a) • f := by
  apply Lp.ext
  filter_upwards [spanField_coe v f,
    (EuclideanSpace.proj (𝕜 := ℝ) (i,a)).coeFn_compLpL (spanField v f),
    Lp.coeFn_smul (v (i,a)) f] with q hv hc hs
  change ((EuclideanSpace.proj (𝕜 := ℝ) (i,a)).compLpL 2 domainMeasure
    (spanField v f)) q = _
  rw [hc,hv,hs]
  change f q * v (i,a) = v (i,a) * f q
  exact mul_comm _ _

def verticalStreamVector (c : PhysicalGradient) : PhysicalGradient :=
  WithLp.toLp 2 (fun j => if j.1 = 1 then -c (0,j.2) else 0)

theorem verticalStreamVector_zero (c : PhysicalGradient) (a : Fin 16) :
    verticalStreamVector c (0,a) = 0 := by simp [verticalStreamVector]

theorem verticalStreamVector_one (c : PhysicalGradient) (a : Fin 16) :
    verticalStreamVector c (1,a) = -c (0,a) := by simp [verticalStreamVector]

theorem slabStream_hasWeakGradient {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (c : PhysicalGradient) :
    HasWeakGradient (fun j => (-c (0,j)) • slabPrimitiveField a ha)
      (spanField (verticalStreamVector c) (slabDerivativeField a ha)) := by
  intro i j test
  rw [componentField_spanField]
  fin_cases i
  · change inner ℝ ((verticalStreamVector c) (0,j) • slabDerivativeField a ha)
      (continuousField test.value) =
      -inner ℝ ((-c (0,j)) • slabPrimitiveField a ha) (continuousField (test.derivative 0))
    rw [verticalStreamVector_zero,zero_smul,inner_zero_left,real_inner_smul_left]
    have h := slabPrimitiveField_horizontal ha test
    simp only [inner_zero_left] at h
    rw [neg_eq_zero.mp h.symm]
    simp
  · change inner ℝ ((verticalStreamVector c) (1,j) • slabDerivativeField a ha)
      (continuousField test.value) =
      -inner ℝ ((-c (0,j)) • slabPrimitiveField a ha) (continuousField (test.derivative 1))
    rw [verticalStreamVector_one,real_inner_smul_left,real_inner_smul_left,
      slabPrimitiveField_vertical ha test]
    ring

theorem curl_verticalStreamVector (c : PhysicalGradient)
    (hc : ∀ j : Fin 16, c (1,j) = 0) : curlOperator (verticalStreamVector c) = c := by
  ext ⟨i,j⟩
  fin_cases i
  · change curlOperator (verticalStreamVector c) (0,j) = c (0,j)
    rw [curlOperator_apply_zero,verticalStreamVector_one,neg_neg]
  · change curlOperator (verticalStreamVector c) (1,j) = c (1,j)
    rw [curlOperator_apply_one,verticalStreamVector_zero,hc j]

theorem curl_spanStream_coe {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (c : PhysicalGradient) (hc : ∀ j : Fin 16, c (1,j) = 0) :
    curlField (spanField (verticalStreamVector c) (slabDerivativeField a ha)) =ᵐ[domainMeasure]
      fun q => slabDerivativeValue a q • c := by
  filter_upwards [curlOperator.coeFn_compLpL
      (spanField (verticalStreamVector c) (slabDerivativeField a ha)),
    spanField_coe (verticalStreamVector c) (slabDerivativeField a ha),
    MemLp.coeFn_toLp (slabDerivativeValue_memLp ha)] with q hcurl hs hd
  change slabDerivativeField a ha q = slabDerivativeValue a q at hd
  change curlField _ q = _ at hcurl
  rw [hcurl,hs,hd,map_smul,curl_verticalStreamVector c hc]

def macroFlux (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (P Q : PhysicalGradient) : PhysicalField :=
  constantField (a • P + (1-a) • Q) +
    curlField (spanField (verticalStreamVector (P-Q)) (slabDerivativeField a ha))

theorem macroFlux_orthogonal (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (P Q : PhysicalGradient)
    (g : PhysicalField) (hg : g ∈ gradientSpace) : inner ℝ (macroFlux a ha P Q) g = 0 := by
  rw [macroFlux,inner_add_left,constant_mean_pairing,gradientSpace_mean_zero g hg,
    inner_zero_right,weakCurl_gradient_zero (slabStream_hasWeakGradient ha (P-Q)) g hg,
    add_zero]

theorem macroFlux_mean (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (P Q : PhysicalGradient) :
    meanField (macroFlux a ha P Q) = a • P + (1-a) • Q := by
  rw [macroFlux,map_add,mean_constantField,
    weakCurl_mean_zero (slabStream_hasWeakGradient ha (P-Q)),add_zero]

theorem macroFlux_coe (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (P Q : PhysicalGradient)
    (hPQ : ∀ j : Fin 16, P (1,j) = Q (1,j)) :
    macroFlux a ha P Q =ᵐ[domainMeasure] fun q =>
      if coordinateRepresentative 1 q < a then P else Q := by
  have hc : ∀ j : Fin 16, (P-Q) (1,j) = 0 := by
    intro j
    change P (1,j) - Q (1,j) = 0
    rw [hPQ j,sub_self]
  filter_upwards [Lp.coeFn_add (constantField (a • P + (1-a) • Q))
      (curlField (spanField (verticalStreamVector (P-Q)) (slabDerivativeField a ha))),
    Lp.coeFn_const 2 domainMeasure (a • P + (1-a) • Q),
    curl_spanStream_coe ha (P-Q) hc] with q hadd hconst hcurl
  change constantField (a • P + (1-a) • Q) q = a • P + (1-a) • Q at hconst
  rw [macroFlux,hadd]
  simp only [Pi.add_apply]
  rw [hconst,hcurl]
  unfold slabDerivativeValue slabIndicator
  split_ifs <;> module

theorem commonVerticalRows_action (B C : HierarchicalLaminates.Lamination.Tensor (Fin 16))
    (hB : CommonVerticalRows B) (hC : CommonVerticalRows C) (F : PhysicalGradient)
    (j : Fin 16) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) B F (1,j) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) C F (1,j) := by
  change Matrix.mulVec B (F : Fin 2 × Fin 16 → ℝ) (1,j) =
    Matrix.mulVec C (F : Fin 2 × Fin 16 → ℝ) (1,j)
  unfold Matrix.mulVec dotProduct
  apply Finset.sum_congr rfl
  intro c _
  rcases c with ⟨i,k⟩
  change B (1,j) (i,k) * F (i,k) = C (1,j) (i,k) * F (i,k)
  rw [hB j i k,hC j i k]

def seedMacroFlux (b : HierarchicalLaminates.Material.PhaseFraction) (θ : ℝ)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (F : PhysicalGradient) : PhysicalField :=
  macroFlux (layerFraction θ) (layerFraction_mem hθ₀ hθ₁)
    (HierarchicalLaminates.Material.effectiveOperator b F)
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (pureTensor θ) F)

theorem seedMacroFlux_orthogonal (b : HierarchicalLaminates.Material.PhaseFraction) (θ : ℝ)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (F : PhysicalGradient)
    (g : PhysicalField) (hg : g ∈ gradientSpace) :
    inner ℝ (seedMacroFlux b θ hθ₀ hθ₁ F) g = 0 :=
  macroFlux_orthogonal _ _ _ _ g hg

theorem seedMacroFlux_mean (b : HierarchicalLaminates.Material.PhaseFraction) (θ : ℝ)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (F : PhysicalGradient) :
    meanField (seedMacroFlux b θ hθ₀ hθ₁ F) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (arithmeticCandidate θ
        (HierarchicalLaminates.Material.effectiveMatrix b)) F := by
  rw [seedMacroFlux,macroFlux_mean,arithmeticCandidate,HierarchicalLaminates.Lamination.matrixAverage]
  simp only [map_add,map_smul,_root_.add_apply,_root_.smul_apply]
  rw [HierarchicalLaminates.Material.effectiveMatrix_operator]

theorem seedMacroFlux_coe (b : HierarchicalLaminates.Material.PhaseFraction) (θ : ℝ)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (F : PhysicalGradient) :
    seedMacroFlux b θ hθ₀ hθ₁ F =ᵐ[domainMeasure] fun q =>
      if coordinateRepresentative 1 q < layerFraction θ then
        HierarchicalLaminates.Material.effectiveOperator b F
      else Matrix.toEuclideanCLM (𝕜 := ℝ) (pureTensor θ) F := by
  apply macroFlux_coe
  intro j
  rw [← HierarchicalLaminates.Material.effectiveMatrix_operator b]
  exact commonVerticalRows_action _ _ (effectiveMatrix_commonVerticalRows b)
    (pureTensor_common_vertical θ) F j

end HierarchicalLaminates.Composition
