module

public import HierarchicalLaminates.Contrast.FullTensor
public import HierarchicalLaminates.Corrector.FullTensor

/-!
# Symmetry of the reduced mean

For `0 ≤ r < 2 / 3`, the full effective tensor of `smoothFraction` is symmetric.
Its reduced parameter `meanResponseMatrix r` is therefore symmetric by the
left-inverse identity for the construction's full-column-rank factor.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.Contrast

/-- Symmetry of the reduced mean follows from the full physical tensor identity. -/
theorem meanResponseMatrix_isHermitian {r : ℝ} (hr : 0 ≤ r) (hrlt : r < 2 / 3) :
    (meanResponseMatrix r).IsHermitian := by
  apply Corrector.materialTensor_reduced_isHermitian
  rw [← effectiveMatrix_eq_materialTensor hr hrlt]
  exact effectiveMatrix_isHermitian hr hrlt Material.smoothFraction

end HierarchicalLaminates.Contrast
