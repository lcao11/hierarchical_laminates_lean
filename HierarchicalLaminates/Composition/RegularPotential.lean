module

public import HierarchicalLaminates.Composition.Interfaces
public import HierarchicalLaminates.Fourier.IntegrationByParts

/-!
# Continuously differentiable periodic potentials
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.Composition

open HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Fourier HierarchicalLaminates.WeakCalculus

structure RegularPotential where
  potential : Fin 16 → C(Domain, ℝ)
  gradient : C(Domain, PhysicalGradient)
  hasPartial : ∀ i a q t, HasDerivAt
    (fun s : ℝ => potential a (coordinateFlow i q s))
    (gradient (coordinateFlow i q t) (i, a)) t

def RegularPotential.field (u : RegularPotential) : PhysicalField :=
  continuousField u.gradient

theorem RegularPotential.weakGradient (u : RegularPotential) :
    HasWeakGradient (fun a => continuousField (u.potential a)) u.field :=
  continuous_hasWeakGradient u.potential u.gradient u.hasPartial

theorem RegularPotential.mem_gradientSpace (u : RegularPotential) :
    u.field ∈ gradientSpace :=
  continuous_gradient_mem u.potential u.gradient u.hasPartial

theorem RegularPotential.curl_orthogonal (u : RegularPotential) (g : PhysicalField)
    (hg : g ∈ gradientSpace) : inner ℝ (curlField u.field) g = 0 :=
  weakCurl_gradient_zero u.weakGradient g hg

theorem RegularPotential.curl_mean_zero (u : RegularPotential) :
    meanField (curlField u.field) = 0 :=
  weakCurl_mean_zero u.weakGradient

def RegularPotential.zero : RegularPotential where
  potential := fun _ => 0
  gradient := 0
  hasPartial := fun _ _ _ t => by simpa using hasDerivAt_const t (0 : ℝ)

def RegularPotential.add (u v : RegularPotential) : RegularPotential where
  potential := fun a => u.potential a + v.potential a
  gradient := u.gradient + v.gradient
  hasPartial := fun i a q t => by
    convert (u.hasPartial i a q t).add (v.hasPartial i a q t) using 1
    simp

def RegularPotential.smul (c : ℝ) (u : RegularPotential) : RegularPotential where
  potential := fun a => c • u.potential a
  gradient := c • u.gradient
  hasPartial := fun i a q t => by
    convert (u.hasPartial i a q t).const_mul c using 1
    simp

@[simp] theorem RegularPotential.field_zero : RegularPotential.zero.field = 0 := by
  simp [RegularPotential.field, RegularPotential.zero]

@[simp] theorem RegularPotential.field_add (u v : RegularPotential) :
    (u.add v).field = u.field + v.field := by
  simp [RegularPotential.field, RegularPotential.add]

@[simp] theorem RegularPotential.field_smul (c : ℝ) (u : RegularPotential) :
    (u.smul c).field = c • u.field := by
  simp [RegularPotential.field, RegularPotential.smul]

end HierarchicalLaminates.Composition
