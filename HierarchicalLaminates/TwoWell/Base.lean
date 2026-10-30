module

public import HierarchicalLaminates.Lamination.ConstitutiveFamily
public import HierarchicalLaminates.Algebra.Parameters

/-!
# Paired energies for two groups of sixteen potentials

The two quadratic branches pair gradient energy with complementary energy.
All tensors act on the full physical gradient space, and both blocks share
one constituent index. Minimizing the paired energy over the invariant
material family defines the rank-one convex minorant.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.TwoWell

open Matrix HierarchicalLaminates HierarchicalLaminates.Lamination

/-- Spatial-first gradients of sixteen scalar potentials. -/
abbrev Gradient16 := Gradient (Fin 16)

/-- Constitutive tensors on the sixteen-potential gradient space. -/
abbrev Tensor16 := Tensor (Fin 16)

/-- The two independent gradient blocks of the thirty-two-potential energy. -/
abbrev PairedGradient := Gradient16 × Gradient16

/-- Clockwise rotation on the spatial rows of each potential. -/
def rotate (F : Gradient16) : Gradient16 := fun p =>
  if p.1 = 0 then F (1, p.2) else -F (0, p.2)

def rotationMatrix : Tensor16 := fun p q =>
  if p.2 = q.2 then
    if p.1 = 0 then (if q.1 = 1 then 1 else 0)
    else (if q.1 = 0 then -1 else 0)
  else 0

/-- Planar complementary dual, using matrix inversion and spatial rotation. -/
def dual (A : Tensor16) : Tensor16 := rotationMatrix * A⁻¹ * rotationMatrixᵀ

/-- Gradient energy and rotated complementary energy for the same tensor. -/
def pairedEnergy (A : Tensor16) (F : PairedGradient) : ℝ :=
  quadraticEnergy A F.1 + quadraticEnergy (dual A) F.2

/-- The quadratic branch associated with the first constituent. -/
def wellZero (F : PairedGradient) : ℝ := pairedEnergy phaseZero F

/-- The quadratic branch associated with the second constituent. -/
def wellOne (F : PairedGradient) : ℝ := pairedEnergy (phaseOne rho) F

/-- The pointwise minimum uses one shared branch index for both blocks. -/
def twoWellEnergy (F : PairedGradient) : ℝ := min (wellZero F) (wellOne F)

/-- The invariant material family used in the energy minimum. -/
def minorant (F : PairedGradient) : ℝ :=
  sInf ((fun A => pairedEnergy A F) '' materialFamily rho)

/-- Compatibility of both blocks across one interface with a shared normal. -/
def Compatible (F₁ F₂ : PairedGradient) : Prop :=
  ∃ (n : LayerNormal) (z₁ z₂ : Fin 16 → ℝ),
    F₁.1 - F₂.1 = normalJump n z₁ ∧ F₁.2 - F₂.2 = normalJump n z₂

/-- Convexity on every rank-one line, including arbitrary real directions. -/
def RankOneConvex (h : PairedGradient → ℝ) : Prop :=
  ∀ (F₁ F₂ : PairedGradient), Compatible F₁ F₂ →
    ∀ a : LayerProportion,
      h ((a : ℝ) • F₁ + (1 - (a : ℝ)) • F₂) ≤
        (a : ℝ) * h F₁ + (1 - (a : ℝ)) * h F₂

end HierarchicalLaminates.TwoWell
