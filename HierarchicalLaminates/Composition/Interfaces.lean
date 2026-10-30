module

public import HierarchicalLaminates.Homogenization.RecoveryGeometry
public import HierarchicalLaminates.Homogenization.LayerAlgebra
public import HierarchicalLaminates.Homogenization.ManuscriptTransport
public import HierarchicalLaminates.WeakCalculus.Curl
public import HierarchicalLaminates.Analysis.Residual

/-! Shared interfaces for exact-fraction composition. -/

@[expose] public section
noncomputable section

namespace HierarchicalLaminates.Composition

open HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material HierarchicalLaminates.Analysis

/-- Response comparison from an admissible trial gradient and equilibrated flux. -/
theorem trial_response_error (b : PhaseFraction) (F : PhysicalGradient)
    (e j : PhysicalField) (he : e - constantField F ∈ gradientSpace)
    (hj : ∀ g ∈ gradientSpace, inner ℝ j g = 0) :
    ‖HierarchicalLaminates.Material.effectiveOperator b F - meanField j‖ ≤
      5 * ‖j - coefficientLaw b e‖ := by
  let eb := cellField gradientSpace (coefficientLaw b) (1 / 4) (by norm_num)
    (coefficientLaw_coercive b) (constantField F)
  have heb : IsCellField gradientSpace (coefficientLaw b) (constantField F) eb :=
    cellField_isCellField _ _ _ _ _ _
  have hde : eb - e ∈ gradientSpace := by
    simpa only [sub_sub_sub_cancel_right] using gradientSpace.sub_mem heb.1 he
  have horth : inner ℝ (coefficientLaw b eb - j) (eb - e) = 0 := by
    rw [inner_sub_left, heb.2 _ hde, hj _ hde, sub_self]
  have hr : j - coefficientLaw b e =
      coefficientLaw b (eb - e) - (coefficientLaw b eb - j) := by
    rw [map_sub]
    abel
  have h := response_error_bound meanField meanField_norm_le
    (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (0 : ℝ) ≤ 1)
    (coefficientLaw_coercive b)
    (fun v => by simpa only [one_mul] using coefficientLaw_norm_le b v)
    (eb - e) (coefficientLaw b eb - j) (j - coefficientLaw b e) hr horth
  have hm : meanField (coefficientLaw b eb - j) =
      HierarchicalLaminates.Material.effectiveOperator b F - meanField j := by
    rw [map_sub]
    rfl
  rw [hm] at h
  norm_num at h ⊢
  exact h

end HierarchicalLaminates.Composition
