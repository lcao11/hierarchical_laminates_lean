module
public import HierarchicalLaminates.GClosure.CompositionActual
public import HierarchicalLaminates.GClosure.FractionHierarchy
public import HierarchicalLaminates.GClosure.DimensionInclusion
/-!
# Closure inclusion and strict separation at every prescribed fraction
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace HierarchicalLaminates.GClosure
open HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material HierarchicalLaminates.Lamination HierarchicalLaminates.Homogenization

theorem laminationClosureAt_subset_GClosure (θ : ℝ) :
    laminationClosureAt phaseZero (phaseOne rho) θ ⊆ GClosure θ := by
  apply inclusion_of_layer_realization ?_ θ
  intro θ₁ θ₂ _ _ B C hB hC n a D hD
  exact layer_mem_of_actual actual_layer_realization hB hC n a hD

theorem strict_inclusion_sixteen (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    laminationClosureAt phaseZero (phaseOne rho) θ ⊂ GClosure θ := by
  obtain ⟨b,hb,hm,_,_,hn⟩ := HierarchicalLaminates.Composition.all_theta_counterexample θ hθ₀ hθ₁
  apply Set.ssubset_iff_exists.mpr
  refine ⟨laminationClosureAt_subset_GClosure θ, effectiveMatrix b, ?_, ?_⟩
  · exact subset_closure ⟨b,hb,hm,rfl⟩
  · intro h
    exact hn (laminationClosureAt_subset_unrestricted _ _ θ h)

theorem all_m_inclusion (m : ℕ) (hm : 16 ≤ m) (θ : ℝ) :
    laminationClosureAt (dimensionPhaseZero m hm) (dimensionPhaseOne m hm) θ ⊆
      genericGClosure (dimensionPhaseZero m hm) (dimensionPhaseOne m hm) θ :=
  dimensional_inclusion_all_m_of_sixteen laminationClosureAt_subset_GClosure m hm θ

theorem all_m_strict_inclusion (m : ℕ) (hm : 16 ≤ m) (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    laminationClosureAt (dimensionPhaseZero m hm) (dimensionPhaseOne m hm) θ ⊂
      genericGClosure (dimensionPhaseZero m hm) (dimensionPhaseOne m hm) θ :=
  dimensional_strict_inclusion_all_m_of_sixteen laminationClosureAt_subset_GClosure m hm θ hθ₀ hθ₁
end HierarchicalLaminates.GClosure
