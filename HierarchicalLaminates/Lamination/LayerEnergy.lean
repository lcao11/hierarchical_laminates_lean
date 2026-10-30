module

public import HierarchicalLaminates.Lamination.QuadraticMinimum
public import Mathlib.Tactic.Push

/-!
# The variational definition of a lamination step

A layer tensor represents the attained minimum of the weighted energy over
all compatible interface jumps, at every mean gradient.
-/

@[expose] public section

namespace HierarchicalLaminates.Lamination

open Matrix

noncomputable section

/-- A spatial normal with arbitrary real coordinates and Euclidean length one. -/
structure LayerNormal where
  coordinates : Fin 2 → ℝ
  unit_length : coordinates 0 ^ 2 + coordinates 1 ^ 2 = 1

/-- A proportion includes both pure-material endpoint cases. -/
abbrev LayerProportion := Set.Icc (0 : ℝ) 1

/-- Flattened gradients retain the spatial index first. -/
abbrev Gradient (m : Type*) := Fin 2 × m → ℝ

abbrev Tensor (m : Type*) := Matrix (Fin 2 × m) (Fin 2 × m) ℝ

variable {m : Type*} [Fintype m]

/-- The compatible jump across a planar interface. -/
def normalJump (n : LayerNormal) (z : m → ℝ) : Gradient m :=
  fun i => n.coordinates i.1 * z i.2

omit [Fintype m] in
theorem normalJump_injective (n : LayerNormal) : Function.Injective (normalJump n :
    (m → ℝ) → Gradient m) := by
  have hnonzero : n.coordinates 0 ≠ 0 ∨ n.coordinates 1 ≠ 0 := by
    by_contra h
    push Not at h
    have hunit := n.unit_length
    simp [h.1, h.2] at hunit
  intro z w hzw
  ext a
  rcases hnonzero with hzero | hone
  · have h := congrFun hzw (0, a)
    exact mul_left_cancel₀ hzero h
  · have h := congrFun hzw (1, a)
    exact mul_left_cancel₀ hone h

def firstLayerField (n : LayerNormal) (weight : ℝ) (F : Gradient m) (z : m → ℝ) :
    Gradient m :=
  F + (1 - weight) • normalJump n z

def secondLayerField (n : LayerNormal) (weight : ℝ) (F : Gradient m) (z : m → ℝ) :
    Gradient m :=
  F - weight • normalJump n z

omit [Fintype m] in
theorem layer_fields_mean (n : LayerNormal) (weight : ℝ) (F : Gradient m) (z : m → ℝ) :
    weight • firstLayerField n weight F z + (1 - weight) • secondLayerField n weight F z = F := by
  ext i
  simp only [firstLayerField, secondLayerField, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

omit [Fintype m] in
theorem layer_fields_jump (n : LayerNormal) (weight : ℝ) (F : Gradient m) (z : m → ℝ) :
    firstLayerField n weight F z - secondLayerField n weight F z = normalJump n z := by
  ext i
  simp only [firstLayerField, secondLayerField, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

def quadraticEnergy (C : Tensor m) (F : Gradient m) : ℝ := F ⬝ᵥ C *ᵥ F

/-- The weighted energy minimized over all compatible interface jumps. -/
def layerEnergy (C₁ C₂ : Tensor m) (n : LayerNormal) (weight : ℝ)
    (F : Gradient m) (z : m → ℝ) : ℝ :=
  weight * quadraticEnergy C₁ (firstLayerField n weight F z) +
    (1 - weight) * quadraticEnergy C₂ (secondLayerField n weight F z)

/-- A tensor represents a layer precisely when it represents the attained
minimum of the compatible-jump energy for every loading. -/
def IsLayerTensor (C₁ C₂ : Tensor m) (n : LayerNormal) (weight : LayerProportion)
    (C : Tensor m) : Prop :=
  C.IsHermitian ∧ ∀ F : Gradient m,
    IsLeast (Set.range (layerEnergy C₁ C₂ n (weight : ℝ) F)) (quadraticEnergy C F)

/-- The variational layer tensor is unique. -/
theorem IsLayerTensor.unique [DecidableEq m] {C₁ C₂ C D : Tensor m}
    {n : LayerNormal} {weight : LayerProportion}
    (hC : IsLayerTensor C₁ C₂ n weight C) (hD : IsLayerTensor C₁ C₂ n weight D) : C = D := by
  apply hermitian_eq_of_quadratic_eq hC.1 hD.1
  intro F
  exact (hC.2 F).unique (hD.2 F)

theorem first_layer_endpoint (C₁ C₂ : Tensor m) (n : LayerNormal)
    (F : Gradient m) (z : m → ℝ) :
    layerEnergy C₁ C₂ n 1 F z = quadraticEnergy C₁ F := by
  simp [layerEnergy, firstLayerField, secondLayerField]

theorem second_layer_endpoint (C₁ C₂ : Tensor m) (n : LayerNormal)
    (F : Gradient m) (z : m → ℝ) :
    layerEnergy C₁ C₂ n 0 F z = quadraticEnergy C₂ F := by
  simp [layerEnergy, firstLayerField, secondLayerField]

end

end HierarchicalLaminates.Lamination
