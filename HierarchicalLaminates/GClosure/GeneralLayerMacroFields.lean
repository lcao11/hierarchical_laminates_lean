module

public import HierarchicalLaminates.GClosure.GeneralLayerFields
public import HierarchicalLaminates.GClosure.GeneralLayerNormal
public import HierarchicalLaminates.GClosure.ObliqueFields
public import HierarchicalLaminates.Composition.MacroFlux

/-!
# Compatible macroscopic fields for layers in periodic integer directions
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open MeasureTheory Set Matrix HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material
  HierarchicalLaminates.Lamination HierarchicalLaminates.WeakCalculus HierarchicalLaminates.Composition HierarchicalLaminates.Homogenization

def verticalGradientVector (z : Fin 16 → ℝ) : PhysicalGradient :=
  WithLp.toLp 2 (fun p => if p.1 = 1 then z p.2 else 0)

theorem slabGradient_hasWeakGradient {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (z : Fin 16 → ℝ) :
    HasWeakGradient (fun c => z c • slabPrimitiveField a ha)
      (spanField (verticalGradientVector z) (slabDerivativeField a ha)) := by
  intro i c test
  rw [componentField_spanField]
  fin_cases i
  · change inner ℝ ((0 : ℝ) • slabDerivativeField a ha) (continuousField test.value) =
      -inner ℝ (z c • slabPrimitiveField a ha) (continuousField (test.derivative 0))
    rw [zero_smul,inner_zero_left,real_inner_smul_left]
    have h := slabPrimitiveField_horizontal ha test
    simp only [inner_zero_left] at h
    rw [neg_eq_zero.mp h.symm]
    simp
  · change inner ℝ (z c • slabDerivativeField a ha) (continuousField test.value) =
      -inner ℝ (z c • slabPrimitiveField a ha) (continuousField (test.derivative 1))
    rw [real_inner_smul_left,real_inner_smul_left,slabPrimitiveField_vertical ha test]
    ring

def normalPhysical (n : LayerNormal) (z : Fin 16 → ℝ) : PhysicalGradient :=
  WithLp.toLp 2 (normalJump n z)

theorem spatialGradientMap_vertical_normal (R : TorusCoordinates) (z : Fin 16 → ℝ) :
    spatialGradientMap R.matrix (verticalGradientVector (fun c => z c / coordinateScale R)) =
      normalPhysical (coordinateNormal R) z := by
  ext ⟨i,c⟩
  change (R.matrix 0 i : ℝ) * 0 + (R.matrix 1 i : ℝ) * (z c / coordinateScale R) =
    ((R.matrix 1 i : ℝ) / coordinateScale R) * z c
  ring

def obliqueSlabGradient (R : TorusCoordinates) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (z : Fin 16 → ℝ) : PhysicalField :=
  R.gradientPullback (spanField (verticalGradientVector (fun c => z c / coordinateScale R))
    (slabDerivativeField a ha))

theorem obliqueSlabGradient_mem (R : TorusCoordinates) (a : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (z : Fin 16 → ℝ) :
    obliqueSlabGradient R a ha z ∈ gradientSpace := by
  apply R.gradientPullback_mem
  exact weakGradientSpace.le_topologicalClosure
    ⟨_,slabGradient_hasWeakGradient ha (fun c => z c / coordinateScale R)⟩

theorem obliqueSlabGradient_coe (R : TorusCoordinates) (a : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (z : Fin 16 → ℝ) :
    obliqueSlabGradient R a ha z =ᵐ[domainMeasure] fun q =>
      slabDerivativeValue a (R.equiv q) • normalPhysical (coordinateNormal R) z := by
  have hp := R.measurePreserving.quasiMeasurePreserving
  filter_upwards [R.gradientPullback_coe
      (spanField (verticalGradientVector (fun c => z c / coordinateScale R))
        (slabDerivativeField a ha)),
    hp.ae (spanField_coe (verticalGradientVector (fun c => z c / coordinateScale R))
      (slabDerivativeField a ha)),
    hp.ae (MemLp.coeFn_toLp (slabDerivativeValue_memLp ha))]
      with q hG hs hd
  change obliqueSlabGradient R a ha z q = _ at hG
  change slabDerivativeField a ha (R.equiv q) = _ at hd
  rw [hG,hs,hd,map_smul,spatialGradientMap_vertical_normal]

def firstPhysicalLayerField (B C : PhysicalTensor) (n : LayerNormal) (a : ℝ)
    (F : PhysicalGradient) : PhysicalGradient :=
  WithLp.toLp 2 (firstOptimalField B C n a (F : Gradient (Fin 16)))

def secondPhysicalLayerField (B C : PhysicalTensor) (n : LayerNormal) (a : ℝ)
    (F : PhysicalGradient) : PhysicalGradient :=
  WithLp.toLp 2 (secondOptimalField B C n a (F : Gradient (Fin 16)))

def firstPhysicalLayerFlux (B C : PhysicalTensor) (n : LayerNormal) (a : ℝ)
    (F : PhysicalGradient) : PhysicalGradient :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) B (firstPhysicalLayerField B C n a F)

def secondPhysicalLayerFlux (B C : PhysicalTensor) (n : LayerNormal) (a : ℝ)
    (F : PhysicalGradient) : PhysicalGradient :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) C (secondPhysicalLayerField B C n a F)

def generalLayerMacroField (R : TorusCoordinates) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (B C : PhysicalTensor) (F : PhysicalGradient) : PhysicalField :=
  constantField F + obliqueSlabGradient R a ha
    (optimalLayerJump B C (coordinateNormal R) a (F : Gradient (Fin 16)))

theorem generalLayerMacroField_admissible (R : TorusCoordinates) (a : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (B C : PhysicalTensor) (F : PhysicalGradient) :
    generalLayerMacroField R a ha B C F - constantField F ∈ gradientSpace := by
  simpa only [generalLayerMacroField,add_sub_cancel_left] using
    obliqueSlabGradient_mem R a ha
      (optimalLayerJump B C (coordinateNormal R) a (F : Gradient (Fin 16)))

theorem generalLayerMacroField_coe (R : TorusCoordinates) (a : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (B C : PhysicalTensor) (F : PhysicalGradient) :
    generalLayerMacroField R a ha B C F =ᵐ[domainMeasure] fun q =>
      if HierarchicalLaminates.Binary.coordinateRepresentative 1 (R.equiv q) < a then
        firstPhysicalLayerField B C (coordinateNormal R) a F
      else secondPhysicalLayerField B C (coordinateNormal R) a F := by
  filter_upwards [Lp.coeFn_add (constantField F)
      (obliqueSlabGradient R a ha (optimalLayerJump B C (coordinateNormal R) a F)),
    Lp.coeFn_const 2 domainMeasure F,
    obliqueSlabGradient_coe R a ha (optimalLayerJump B C (coordinateNormal R) a F)]
      with q hadd hF hG
  change constantField F q = F at hF
  rw [generalLayerMacroField,hadd]
  simp only [Pi.add_apply]
  rw [hF,hG]
  unfold slabDerivativeValue slabIndicator
  split_ifs with hq
  · ext p
    simp [firstPhysicalLayerField,firstOptimalField,firstLayerField,normalPhysical]
  · ext p
    simp [secondPhysicalLayerField,secondOptimalField,secondLayerField,normalPhysical]
    ring

theorem physical_flux_normal_zero {B C : PhysicalTensor} (hB : B.PosDef) (hC : C.PosDef)
    (n : LayerNormal) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (F : PhysicalGradient) :
    (normalMatrix n)ᵀ *ᵥ
      ((firstPhysicalLayerFlux B C n a F - secondPhysicalLayerFlux B C n a F) :
        Gradient (Fin 16)) = 0 := by
  change (normalMatrix n)ᵀ *ᵥ
    (B *ᵥ firstOptimalField B C n a F - C *ᵥ secondOptimalField B C n a F) = 0
  rw [Matrix.mulVec_sub,optimal_normal_flux_match hB hC n ha.1 ha.2,sub_self]

theorem curl_normalPhysical_tangent (n : LayerNormal) (J : PhysicalGradient)
    (hJ : (normalMatrix n)ᵀ *ᵥ (J : Gradient (Fin 16)) = 0) :
    curlOperator (normalPhysical n (tangentAmplitude n (J : Gradient (Fin 16)))) = J := by
  have h := tangentField_eq_of_normal_zero n (J : Gradient (Fin 16)) hJ
  ext ⟨i,c⟩
  have hc := congrFun h (i,c)
  fin_cases i
  · change curlOperator (normalPhysical n (tangentAmplitude n J)) (0,c) = J (0,c)
    rw [curlOperator_apply_zero]
    change -(n.coordinates 1 * tangentAmplitude n J c) = J (0,c)
    simpa [tangentField] using hc
  · change curlOperator (normalPhysical n (tangentAmplitude n J)) (1,c) = J (1,c)
    rw [curlOperator_apply_one]
    change n.coordinates 0 * tangentAmplitude n J c = J (1,c)
    simpa [tangentField] using hc

def generalLayerMacroFlux (R : TorusCoordinates) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (B C : PhysicalTensor) (F : PhysicalGradient) : PhysicalField :=
  let P := firstPhysicalLayerFlux B C (coordinateNormal R) a F
  let Q := secondPhysicalLayerFlux B C (coordinateNormal R) a F
  constantField (a • P + (1-a) • Q) +
    curlField (obliqueSlabGradient R a ha
      (tangentAmplitude (coordinateNormal R) ((P-Q) : Gradient (Fin 16))))

theorem generalLayerMacroFlux_orthogonal (R : TorusCoordinates) (a : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (B C : PhysicalTensor) (F : PhysicalGradient)
    (g : PhysicalField) (hg : g ∈ gradientSpace) :
    inner ℝ (generalLayerMacroFlux R a ha B C F) g = 0 := by
  dsimp only [generalLayerMacroFlux]
  rw [inner_add_left,constant_mean_pairing,gradientSpace_mean_zero g hg,inner_zero_right,
    closedGradient_curl_orthogonal _ (obliqueSlabGradient_mem R a ha _) g hg,add_zero]

theorem generalLayerMacroFlux_mean (R : TorusCoordinates) (a : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) {B C : PhysicalTensor} (hB : B.IsHermitian) (hC : C.IsHermitian)
    (F : PhysicalGradient) :
    meanField (generalLayerMacroFlux R a ha B C F) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (computedLayerTensor B C (coordinateNormal R) a) F := by
  dsimp only [generalLayerMacroFlux]
  rw [map_add,mean_constantField,closedGradient_curl_mean_zero _ (obliqueSlabGradient_mem R a ha _),add_zero]
  ext p
  exact congrFun (optimal_flux_mean hB hC (coordinateNormal R) a F) p

theorem generalLayerMacroFlux_coe (R : TorusCoordinates) (a : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) {B C : PhysicalTensor} (hB : B.PosDef) (hC : C.PosDef)
    (F : PhysicalGradient) :
    generalLayerMacroFlux R a ha B C F =ᵐ[domainMeasure] fun q =>
      if HierarchicalLaminates.Binary.coordinateRepresentative 1 (R.equiv q) < a then
        firstPhysicalLayerFlux B C (coordinateNormal R) a F
      else secondPhysicalLayerFlux B C (coordinateNormal R) a F := by
  let P := firstPhysicalLayerFlux B C (coordinateNormal R) a F
  let Q := secondPhysicalLayerFlux B C (coordinateNormal R) a F
  let z := tangentAmplitude (coordinateNormal R) ((P-Q) : Gradient (Fin 16))
  have hJ := physical_flux_normal_zero hB hC (coordinateNormal R) a ha F
  have hz : curlOperator (normalPhysical (coordinateNormal R) z) = P-Q := by
    exact curl_normalPhysical_tangent (coordinateNormal R) (P-Q) hJ
  filter_upwards [Lp.coeFn_add (constantField (a • P+(1-a) • Q))
      (curlField (obliqueSlabGradient R a ha z)),
    Lp.coeFn_const 2 domainMeasure (a • P+(1-a) • Q),
    curlOperator.coeFn_compLpL (obliqueSlabGradient R a ha z),
    obliqueSlabGradient_coe R a ha z] with q hadd hconst hcurl hG
  change constantField (a • P+(1-a) • Q) q = _ at hconst
  change curlField (obliqueSlabGradient R a ha z) q = _ at hcurl
  change generalLayerMacroFlux R a ha B C F q = _ at hadd
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hconst,hcurl,hG,map_smul,hz]
  unfold slabDerivativeValue slabIndicator
  split_ifs <;> dsimp [P,Q] <;> module

end HierarchicalLaminates.GClosure
