module

public import HierarchicalLaminates.Fourier.SequenceOperators
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Uniform synthesis of real coefficient sequences

For kernels of uniform norm at most one, absolutely summable coefficients
give a continuous field with values in a real Banach space. Periodic cosine
and sine kernels satisfy these hypotheses.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Fourier

variable {ι X E : Type*} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def synthesisTerm (K : ι → C(X, ℝ)) (f : Coefficients ι E) (i : ι) : C(X, E) :=
  K i • ContinuousMap.const X (f i)

omit [CompleteSpace E] in
theorem synthesisTerm_norm_le (K : ι → C(X, ℝ)) (hK : ∀ i, ‖K i‖ ≤ 1)
    (f : Coefficients ι E) (i : ι) : ‖synthesisTerm K f i‖ ≤ ‖f i‖ := by
  rw [synthesisTerm, ContinuousMap.norm_smul_const]
  simpa using mul_le_mul_of_nonneg_right (hK i) (norm_nonneg (f i))

omit [CompleteSpace E] in
theorem synthesisTerm_summable_norm (K : ι → C(X, ℝ)) (hK : ∀ i, ‖K i‖ ≤ 1)
    (f : Coefficients ι E) : Summable (fun i => ‖synthesisTerm K f i‖) :=
  (coefficients_summable_norm f).of_nonneg_of_le (fun _ => norm_nonneg _)
    (synthesisTerm_norm_le K hK f)

theorem synthesisTerm_summable (K : ι → C(X, ℝ)) (hK : ∀ i, ‖K i‖ ≤ 1)
    (f : Coefficients ι E) : Summable (synthesisTerm K f) :=
  Summable.of_norm (synthesisTerm_summable_norm K hK f)

/-- The series converges in the uniform norm, so its sum is continuous. -/
def continuousSynthesis (K : ι → C(X, ℝ)) (f : Coefficients ι E) : C(X, E) :=
  ∑' i, synthesisTerm K f i

omit [CompleteSpace E] in
theorem continuousSynthesis_norm_le (K : ι → C(X, ℝ)) (hK : ∀ i, ‖K i‖ ≤ 1)
    (f : Coefficients ι E) : ‖continuousSynthesis K f‖ ≤ ‖f‖ := by
  calc
    ‖continuousSynthesis K f‖ ≤ ∑' i, ‖synthesisTerm K f i‖ :=
      norm_tsum_le_tsum_norm (synthesisTerm_summable_norm K hK f)
    _ ≤ ∑' i, ‖f i‖ :=
      (synthesisTerm_summable_norm K hK f).tsum_le_tsum
        (synthesisTerm_norm_le K hK f) (coefficients_summable_norm f)
    _ = ‖f‖ := (coefficients_norm_eq f).symm

omit [CompactSpace X] [CompleteSpace E] in
theorem synthesisTerm_add (K : ι → C(X, ℝ)) (f g : Coefficients ι E) (i : ι) :
    synthesisTerm K (f + g) i = synthesisTerm K f i + synthesisTerm K g i := by
  ext x
  simp [synthesisTerm, smul_add]

omit [CompactSpace X] [CompleteSpace E] in
theorem synthesisTerm_smul (K : ι → C(X, ℝ)) (c : ℝ) (f : Coefficients ι E) (i : ι) :
    synthesisTerm K (c • f) i = c • synthesisTerm K f i := by
  ext x
  simp [synthesisTerm, smul_smul, mul_comm]

def synthesisLinear (K : ι → C(X, ℝ)) (hK : ∀ i, ‖K i‖ ≤ 1) :
    Coefficients ι E →ₗ[ℝ] C(X, E) where
  toFun := continuousSynthesis K
  map_add' f g := by
    simpa only [continuousSynthesis, synthesisTerm_add] using
      (synthesisTerm_summable K hK f).tsum_add (synthesisTerm_summable K hK g)
  map_smul' c f := by
    simpa only [continuousSynthesis, synthesisTerm_smul, RingHom.id_apply] using
      (synthesisTerm_summable K hK f).tsum_const_smul c

/-- Uniform synthesis as a bounded real linear map. -/
def synthesisCLM (K : ι → C(X, ℝ)) (hK : ∀ i, ‖K i‖ ≤ 1) :
    Coefficients ι E →L[ℝ] C(X, E) :=
  (synthesisLinear K hK).mkContinuous 1 (fun f => by
    simpa [synthesisLinear] using continuousSynthesis_norm_le K hK f)

@[simp]
theorem synthesisCLM_apply (K : ι → C(X, ℝ)) (hK : ∀ i, ‖K i‖ ≤ 1)
    (f : Coefficients ι E) : synthesisCLM K hK f = continuousSynthesis K f := rfl

theorem pointwiseSynthesis_summable (K : ι → C(X, ℝ)) (hK : ∀ i, ‖K i‖ ≤ 1)
    (f : Coefficients ι E) (x : X) : Summable (fun i => K i x • f i) := by
  simpa only [synthesisTerm, ContinuousMap.evalCLM_apply,
    ContinuousMap.smul_apply', ContinuousMap.const_apply] using
      (ContinuousMap.evalCLM ℝ x).summable (synthesisTerm_summable K hK f)

theorem continuousSynthesis_apply (K : ι → C(X, ℝ)) (hK : ∀ i, ‖K i‖ ≤ 1)
    (f : Coefficients ι E) (x : X) :
    continuousSynthesis K f x = ∑' i, K i x • f i := by
  simpa only [continuousSynthesis, synthesisTerm, ContinuousMap.evalCLM_apply,
    ContinuousMap.smul_apply', ContinuousMap.const_apply] using
      (ContinuousMap.evalCLM ℝ x).map_tsum (synthesisTerm_summable K hK f)

omit [CompleteSpace E] in
theorem continuousSynthesis_pointwise_norm_le (K : ι → C(X, ℝ))
    (hK : ∀ i, ‖K i‖ ≤ 1) (f : Coefficients ι E) (x : X) :
    ‖continuousSynthesis K f x‖ ≤ ‖f‖ :=
  ((continuousSynthesis K f).norm_coe_le_norm x).trans (continuousSynthesis_norm_le K hK f)

end HierarchicalLaminates.Fourier
