module

public import HierarchicalLaminates.Lamination.Hierarchy
public import Mathlib.Tactic.FunProp

/-!
# Separation by the difference of two loading energies
-/

@[expose] public section

namespace HierarchicalLaminates.Lamination

variable {m : Type*} [Fintype m]

def loadingDifference (ξ η : Gradient m) (C : Tensor m) : ℝ :=
  quadraticEnergy C η - quadraticEnergy C ξ

theorem loadingDifference_continuous (ξ η : Gradient m) :
    Continuous (loadingDifference ξ η) := by
  unfold loadingDifference quadraticEnergy Matrix.mulVec dotProduct
  fun_prop

/-- A strict difference of the two physical loading energies excludes a
tensor from the closure of all finite hierarchies, once the universal finite
invariant has been proved for the concrete constituents. -/
theorem positive_difference_excludes_laminate_closure
    {L₀ L₁ C : Tensor m} (ξ η : Gradient m)
    (hinvariant : ∀ B, FiniteLaminate L₀ L₁ B → loadingDifference ξ η B = 0)
    (hpositive : 0 < loadingDifference ξ η C) :
    C ∉ closure (allFiniteLaminates L₀ L₁) := by
  intro hclosure
  have hzero := functional_zero_on_closure (loadingDifference ξ η)
    (loadingDifference_continuous ξ η) hinvariant hclosure
  linarith

end HierarchicalLaminates.Lamination
