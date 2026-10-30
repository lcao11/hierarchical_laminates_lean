module
public import HierarchicalLaminates.GClosure.GClosureBounds
public import HierarchicalLaminates.GClosure.GeneralLayerNormal
public import HierarchicalLaminates.GClosure.DirectionApproximation
public import Mathlib.Topology.Sequences
/-!
# Passing periodic layer recovery to the G-closure
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace HierarchicalLaminates.GClosure
open Matrix MeasureTheory Filter HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material
  HierarchicalLaminates.Lamination HierarchicalLaminates.Homogenization
local instance : FirstCountableTopology (Tensor (Fin 16)) := by
  change FirstCountableTopology ((Fin 2 × Fin 16) → (Fin 2 × Fin 16) → ℝ)
  infer_instance
def ActualLayerRealization : Prop :=
  ∀ (b c : PhaseFraction), IsBinary b → IsBinary c →
    ∀ (R : TorusCoordinates) (a : ℝ), 0 < a → a < 1 →
      computedLayerTensor (effectiveMatrix b) (effectiveMatrix c) (coordinateNormal R) a ∈
        GClosure (a * phaseMean b + (1-a) * phaseMean c)

theorem integer_layer_mem_of_actual (hactual : ActualLayerRealization)
    {θ₁ θ₂ : ℝ} {B C : Tensor (Fin 16)} (hB : B ∈ GClosure θ₁) (hC : C ∈ GClosure θ₂)
    (R : TorusCoordinates) (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) :
    computedLayerTensor B C (coordinateNormal R) a ∈ GClosure (a*θ₁+(1-a)*θ₂) := by
  obtain ⟨Bs, hBs, hBlim⟩ := mem_closure_iff_seq_limit.mp hB
  obtain ⟨Cs, hCs, hClim⟩ := mem_closure_iff_seq_limit.mp hC
  choose b hb hmB heB using hBs
  choose c hc hmC heC using hCs
  have hlim : Tendsto (fun j : ℕ => computedLayerTensor (Bs j) (Cs j) (coordinateNormal R) a)
      atTop (nhds (computedLayerTensor B C (coordinateNormal R) a)) :=
    computedLayerTensor_tendsto hBlim hClim tendsto_const_nhds tendsto_const_nhds
    (GClosure_posDef hB) (GClosure_posDef hC) ha₀.le ha₁.le
  apply isClosed_closure.mem_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro j
  have h := hactual (b j) (c j) (hb j) (hc j) R a ha₀ ha₁
  simpa only [GClosure, hmB j, hmC j, heB j, heC j] using h
theorem all_normals_layer_mem_of_actual (hactual : ActualLayerRealization)
    {θ₁ θ₂ : ℝ} {B C : Tensor (Fin 16)} (hB : B ∈ GClosure θ₁) (hC : C ∈ GClosure θ₂)
    (n : LayerNormal) (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) :
    computedLayerTensor B C n a ∈ GClosure (a*θ₁+(1-a)*θ₂) := by
  obtain ⟨R, hR⟩ := exists_coordinateNormal_sequence n
  have hlim : Tendsto (fun j : ℕ => computedLayerTensor B C (coordinateNormal (R j)) a)
      atTop (nhds (computedLayerTensor B C n a)) :=
    computedLayerTensor_tendsto tendsto_const_nhds tendsto_const_nhds hR tendsto_const_nhds
      (GClosure_posDef hB) (GClosure_posDef hC) ha₀.le ha₁.le
  apply isClosed_closure.mem_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro j
  simpa only [GClosure] using integer_layer_mem_of_actual hactual hB hC (R j) a ha₀ ha₁

theorem computed_layer_mem_of_actual (hactual : ActualLayerRealization)
    {θ₁ θ₂ : ℝ} {B C : Tensor (Fin 16)} (hB : B ∈ GClosure θ₁) (hC : C ∈ GClosure θ₂)
    (n : LayerNormal) (a : LayerProportion) :
    computedLayerTensor B C n (a : ℝ) ∈ GClosure ((a : ℝ)*θ₁+(1-(a : ℝ))*θ₂) := by
  by_cases h₀ : (a : ℝ) = 0
  · simpa [h₀, computedLayerTensor, matrixAverage] using hC
  by_cases h₁ : (a : ℝ) = 1
  · simpa [h₁, computedLayerTensor, matrixAverage] using hB
  exact all_normals_layer_mem_of_actual hactual hB hC n a
    (lt_of_le_of_ne a.property.1 (Ne.symm h₀)) (lt_of_le_of_ne a.property.2 h₁)

theorem layer_mem_of_actual (hactual : ActualLayerRealization)
    {θ₁ θ₂ : ℝ} {B C D : Tensor (Fin 16)} (hB : B ∈ GClosure θ₁) (hC : C ∈ GClosure θ₂)
    (n : LayerNormal) (a : LayerProportion) (hD : IsLayerTensor B C n a D) :
    D ∈ GClosure ((a : ℝ)*θ₁+(1-(a : ℝ))*θ₂) := by
  have hcanonical := computedLayerTensor_represents_minimum (GClosure_posDef hB) (GClosure_posDef hC) n a
  rw [hD.unique hcanonical]
  exact computed_layer_mem_of_actual hactual hB hC n a
end HierarchicalLaminates.GClosure
