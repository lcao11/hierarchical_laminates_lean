module

public import HierarchicalLaminates.Lamination.LayerEnergy
public import Mathlib.Tactic.Module

/-!
# Compatible layer fields as energy competitors

A compatible pair of gradients supplies an admissible jump. Its weighted
energy bounds the layer energy at the weighted mean from above. Applying
this inequality to both blocks gives a competitor for the paired energy.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.Lamination

variable {α : Type*} [Fintype α]

/-- A compatible pair is an admissible competitor in the layer-energy minimum. -/
theorem IsLayerTensor.energy_le_of_compatible
    {A B D : Tensor α} {n : LayerNormal} {a : LayerProportion}
    (hLayer : IsLayerTensor A B n a D)
    {F₁ F₂ : Gradient α} (z : α → ℝ)
    (hjump : F₁ - F₂ = normalJump n z) :
    quadraticEnergy D ((a : ℝ) • F₁ + (1 - (a : ℝ)) • F₂) ≤
      (a : ℝ) * quadraticEnergy A F₁ +
        (1 - (a : ℝ)) * quadraticEnergy B F₂ := by
  let F := (a : ℝ) • F₁ + (1 - (a : ℝ)) • F₂
  have hfirst : firstLayerField n (a : ℝ) F z = F₁ := by
    rw [firstLayerField, ← hjump]
    dsimp [F]
    module
  have hsecond : secondLayerField n (a : ℝ) F z = F₂ := by
    rw [secondLayerField, ← hjump]
    dsimp [F]
    module
  have hminimum := (hLayer.2 F).2
    (show layerEnergy A B n (a : ℝ) F z ∈
      Set.range (layerEnergy A B n (a : ℝ) F) from ⟨z, rfl⟩)
  simpa only [layerEnergy, hfirst, hsecond] using hminimum

end HierarchicalLaminates.Lamination
