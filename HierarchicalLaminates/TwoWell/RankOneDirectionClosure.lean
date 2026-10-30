module

public import HierarchicalLaminates.TwoWell.LaminateJensen

/-!
# Extension from integer torus normals to every real normal

For a continuous integrand, density of integer torus normals extends the
two-state Jensen inequalities to every real normal. Both gradient blocks use
the same spatial direction throughout the approximation.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.TwoWell

open Set Filter Periodic HierarchicalLaminates.Composition GClosure Lamination

theorem pairedNormalJump_continuous (z₁ z₂ : Fin 16 → ℝ) :
    Continuous (fun n : LayerNormal => pairedNormalJump n z₁ z₂) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro p
    exact ((continuous_apply p.1).comp normalCoordinates_continuous).mul continuous_const
  · apply continuous_pi
    intro p
    exact ((continuous_apply p.1).comp normalCoordinates_continuous).mul continuous_const

theorem realNormal_jensen_of_coordinateNormal {h : PairedGradient → ℝ}
    (hc : Continuous h)
    (hh : ∀ (R : TorusCoordinates) (F : PairedGradient) (z₁ z₂ : Fin 16 → ℝ)
      (a : LayerProportion),
      h F ≤ (a : ℝ)*h (F+(1-(a : ℝ)) • pairedNormalJump (coordinateNormal R) z₁ z₂)+
        (1-(a : ℝ))*h (F-(a : ℝ) • pairedNormalJump (coordinateNormal R) z₁ z₂))
    (n : LayerNormal) (F : PairedGradient) (z₁ z₂ : Fin 16 → ℝ) (a : LayerProportion) :
    h F ≤ (a : ℝ)*h (F+(1-(a : ℝ)) • pairedNormalJump n z₁ z₂)+
      (1-(a : ℝ))*h (F-(a : ℝ) • pairedNormalJump n z₁ z₂) := by
  obtain ⟨R,hR⟩ := exists_coordinateNormal_sequence n
  have hJ := pairedNormalJump_continuous z₁ z₂
  have hrhs : Continuous (fun n : LayerNormal =>
      (a : ℝ)*h (F+(1-(a : ℝ)) • pairedNormalJump n z₁ z₂)+
        (1-(a : ℝ))*h (F-(a : ℝ) • pairedNormalJump n z₁ z₂)) :=
    by fun_prop
  exact ge_of_tendsto (hrhs.continuousAt.tendsto.comp hR)
    (Filter.Eventually.of_forall (fun j => hh (R j) F z₁ z₂ a))

theorem rankOneConvex_of_continuous_coordinateNormal_jensen {h : PairedGradient → ℝ}
    (hc : Continuous h)
    (hh : ∀ (R : TorusCoordinates) (F : PairedGradient) (z₁ z₂ : Fin 16 → ℝ)
      (a : LayerProportion),
      h F ≤ (a : ℝ)*h (F+(1-(a : ℝ)) • pairedNormalJump (coordinateNormal R) z₁ z₂)+
        (1-(a : ℝ))*h (F-(a : ℝ) • pairedNormalJump (coordinateNormal R) z₁ z₂)) :
    RankOneConvex h := by
  intro F₁ F₂ hcomp a
  obtain ⟨n,z₁,z₂,h₁,h₂⟩ := hcomp
  have hJ : pairedNormalJump n z₁ z₂ = F₁-F₂ := Prod.ext h₁.symm h₂.symm
  have hp : ((a : ℝ) • F₁+(1-(a : ℝ)) • F₂)+
      (1-(a : ℝ)) • pairedNormalJump n z₁ z₂ = F₁ := by
    rw [hJ]
    module
  have hm : ((a : ℝ) • F₁+(1-(a : ℝ)) • F₂)-
      (a : ℝ) • pairedNormalJump n z₁ z₂ = F₂ := by
    rw [hJ]
    module
  simpa only [hp,hm] using realNormal_jensen_of_coordinateNormal hc hh n
    ((a : ℝ) • F₁+(1-(a : ℝ)) • F₂) z₁ z₂ a

end HierarchicalLaminates.TwoWell
