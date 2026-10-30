module

public import HierarchicalLaminates.GClosure.DimensionPeriod

/-! The sixteen-component realization inclusion transports to every enlarged system. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material HierarchicalLaminates.Lamination
  HierarchicalLaminates.Homogenization

theorem dimensional_inclusion_all_m_of_sixteen
    (hinclusion : ∀ θ : ℝ, laminationClosureAt phaseZero (phaseOne rho) θ ⊆ GClosure θ)
    (m : ℕ) (hm : 16 ≤ m) (θ : ℝ) :
    laminationClosureAt (dimensionPhaseZero m hm) (dimensionPhaseOne m hm) θ ⊆
      genericGClosure (dimensionPhaseZero m hm) (dimensionPhaseOne m hm) θ := by
  intro C hC
  let e := dimensionEquiv m hm
  have hpull := laminationClosureAt_reindex e.symm (dimensionPhaseZero m hm)
    (dimensionPhaseOne m hm) θ hC
  change reindexTensor e.symm C ∈ laminationClosureAt
    (reindexTensor e.symm (reindexTensor e (extendTensor phaseZero)))
    (reindexTensor e.symm (reindexTensor e (extendTensor (phaseOne rho)))) θ at hpull
  rw [reindexTensor_symm_left,reindexTensor_symm_left] at hpull
  have hext := dimensional_inclusion_of_sixteen (β := Fin (m-16)) hinclusion θ hpull
  have hpush := genericGClosure_reindex e (extendTensor phaseZero)
    (extendTensor (phaseOne rho)) θ hext
  rw [reindexTensor_symm] at hpush
  exact hpush

theorem dimensional_strict_inclusion_all_m_of_sixteen
    (hinclusion : ∀ θ : ℝ, laminationClosureAt phaseZero (phaseOne rho) θ ⊆ GClosure θ)
    (m : ℕ) (hm : 16 ≤ m) (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    laminationClosureAt (dimensionPhaseZero m hm) (dimensionPhaseOne m hm) θ ⊂
      genericGClosure (dimensionPhaseZero m hm) (dimensionPhaseOne m hm) θ := by
  obtain ⟨b,hb,hmn,he,hp,hn⟩ := all_m_counterexample m hm θ hθ₀ hθ₁
  apply Set.ssubset_iff_exists.mpr
  refine ⟨dimensional_inclusion_all_m_of_sixteen hinclusion m hm θ,
    dimensionEffective m hm b,?_,?_⟩
  · exact subset_closure ⟨reindexTensor_isHermitian _
      (extendTensor_isHermitian (effectiveMatrix_isHermitian b)),b,hb,hmn,he⟩
  · intro hmem
    exact hn (laminationClosureAt_subset_unrestricted _ _ θ hmem)

end HierarchicalLaminates.GClosure
