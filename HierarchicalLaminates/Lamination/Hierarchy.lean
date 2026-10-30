module

public import HierarchicalLaminates.Lamination.LayerEnergy
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Instances.Matrix

/-!
# Finite hierarchies and their closure

Every node permits any real unit normal and any proportion in the closed
unit interval. Iterating the variational layer operation gives hierarchies
of arbitrary finite depth.
-/

@[expose] public section

namespace HierarchicalLaminates.Lamination

variable {m : Type*} [Fintype m]

inductive FiniteLaminate (L₀ L₁ : Tensor m) : Tensor m → Prop
  | phaseZero : FiniteLaminate L₀ L₁ L₀
  | phaseOne : FiniteLaminate L₀ L₁ L₁
  | layer {C₁ C₂ C : Tensor m} (n : LayerNormal) (weight : LayerProportion)
      (first : FiniteLaminate L₀ L₁ C₁) (second : FiniteLaminate L₀ L₁ C₂)
      (representsMinimum : IsLayerTensor C₁ C₂ n weight C) : FiniteLaminate L₀ L₁ C

def allFiniteLaminates (L₀ L₁ : Tensor m) : Set (Tensor m) :=
  {C | FiniteLaminate L₀ L₁ C}

/-- A family containing both phases and stable under every layering step
contains every finite laminate. -/
theorem finiteLaminate_mem_of_stable {L₀ L₁ : Tensor m} {K : Set (Tensor m)}
    (h₀ : L₀ ∈ K) (h₁ : L₁ ∈ K)
    (hstep : ∀ {C₁ C₂ C : Tensor m} (n : LayerNormal) (weight : LayerProportion),
      C₁ ∈ K → C₂ ∈ K → IsLayerTensor C₁ C₂ n weight C → C ∈ K)
    {C : Tensor m} (hC : FiniteLaminate L₀ L₁ C) : C ∈ K := by
  induction hC with
  | phaseZero => exact h₀
  | phaseOne => exact h₁
  | layer n weight _ _ hminimum ih₁ ih₂ => exact hstep n weight ih₁ ih₂ hminimum

/-- A continuous separating functional which vanishes on all finite
hierarchies also vanishes on their entire tensor closure. -/
theorem functional_zero_on_closure {L₀ L₁ : Tensor m} (ℓ : Tensor m → ℝ)
    (hcontinuous : Continuous ℓ)
    (hfinite : ∀ C, FiniteLaminate L₀ L₁ C → ℓ C = 0)
    {C : Tensor m} (hC : C ∈ closure (allFiniteLaminates L₀ L₁)) : ℓ C = 0 := by
  have hsubset : allFiniteLaminates L₀ L₁ ⊆ {B | ℓ B = 0} := by
    intro B hB
    exact hfinite B hB
  exact closure_minimal hsubset (isClosed_eq hcontinuous continuous_const) hC

end HierarchicalLaminates.Lamination
