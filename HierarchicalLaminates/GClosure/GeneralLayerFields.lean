module

public import HierarchicalLaminates.GClosure.GeneralLayerAlgebra
public import HierarchicalLaminates.Composition.FourierApproximation

/-! Equilibrium for rotated fields in the closed weak-gradient space. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.WeakCalculus HierarchicalLaminates.Composition

theorem closedGradient_curl_orthogonal (v : PhysicalField) (hv : v ∈ gradientSpace)
    (g : PhysicalField) (hg : g ∈ gradientSpace) : inner ℝ (curlField v) g = 0 := by
  let L : PhysicalField →L[ℝ] ℝ := (innerSL ℝ g).comp curlField
  have hsub : regularGradients ≤ L.ker := by
    rintro w ⟨u, rfl⟩
    change inner ℝ g (curlField u.field) = 0
    rw [real_inner_comm]
    exact u.curl_orthogonal g hg
  have hv' : v ∈ regularGradients.topologicalClosure := by
    rw [regularGradients_closure_eq]
    exact hv
  have h := regularGradients.topologicalClosure_minimal hsub L.isClosed_ker hv'
  change inner ℝ g (curlField v) = 0 at h
  rwa [real_inner_comm] at h

theorem closedGradient_curl_mean_zero (v : PhysicalField) (hv : v ∈ gradientSpace) :
    meanField (curlField v) = 0 := by
  rw [curlField, meanField_comp, gradientSpace_mean_zero v hv, map_zero]

/-- A compatible layer correction has zero mean under the prescribed weighted average. -/
theorem optimal_gradient_corrections_mean {m : Type*} [Fintype m] [DecidableEq m]
    (B C : HierarchicalLaminates.Lamination.Tensor m) (n : HierarchicalLaminates.Lamination.LayerNormal)
    (a : ℝ) (F : HierarchicalLaminates.Lamination.Gradient m) :
    a • (firstOptimalField B C n a F - F) +
      (1-a) • (secondOptimalField B C n a F - F) = 0 := by
  have h := optimal_fields_mean B C n a F
  have heq : a • (firstOptimalField B C n a F - F) +
      (1-a) • (secondOptimalField B C n a F - F) =
      (a • firstOptimalField B C n a F + (1-a) • secondOptimalField B C n a F) - F := by
    module
  rw [heq, h, sub_self]

end HierarchicalLaminates.GClosure
