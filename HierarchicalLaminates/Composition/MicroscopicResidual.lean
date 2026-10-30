module

public import HierarchicalLaminates.Composition.RegularPotential

/-!
# Regular microscopic trial fields and seed cell fields
-/

@[expose] public section
noncomputable section

namespace HierarchicalLaminates.Composition

open HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material HierarchicalLaminates.Analysis
  HierarchicalLaminates.WeakCalculus

def microscopicCell (b : PhaseFraction) (F : PhysicalGradient) : PhysicalField :=
  cellField gradientSpace (coefficientLaw b) (1 / 4) (by norm_num)
    (coefficientLaw_coercive b) (constantField F)

def microscopicGradient (b : PhaseFraction) (F : PhysicalGradient) : PhysicalField :=
  microscopicCell b F - constantField F

def microscopicFlux (b : PhaseFraction) (F : PhysicalGradient) : PhysicalField :=
  coefficientLaw b (microscopicCell b F)

theorem microscopicGradient_mem (b : PhaseFraction) (F : PhysicalGradient) :
    microscopicGradient b F ∈ gradientSpace :=
  (cellField_isCellField _ _ _ _ _ _).1

theorem microscopicFlux_orthogonal (b : PhaseFraction) (F : PhysicalGradient)
    (g : PhysicalField) (hg : g ∈ gradientSpace) :
    inner ℝ (microscopicFlux b F) g = 0 :=
  (cellField_isCellField _ _ _ _ _ _).2 g hg

theorem microscopicFlux_mean (b : PhaseFraction) (F : PhysicalGradient) :
    meanField (microscopicFlux b F) = HierarchicalLaminates.Material.effectiveOperator b F := rfl

theorem centered_microscopicFlux_mean (b : PhaseFraction) (F : PhysicalGradient) :
    meanField (microscopicFlux b F - constantField (HierarchicalLaminates.Material.effectiveOperator b F)) = 0 := by
  rw [map_sub, microscopicFlux_mean, mean_constantField, sub_self]

theorem centered_microscopicFlux_orthogonal (b : PhaseFraction) (F : PhysicalGradient)
    (g : PhysicalField) (hg : g ∈ gradientSpace) :
    inner ℝ (microscopicFlux b F - constantField (HierarchicalLaminates.Material.effectiveOperator b F)) g = 0 := by
  rw [inner_sub_left, microscopicFlux_orthogonal b F g hg,
    constant_mean_pairing, gradientSpace_mean_zero g hg, inner_zero_right, sub_self]

def regularMicroscopicResidual (b : PhaseFraction) (F : PhysicalGradient)
    (u ψ : RegularPotential) : PhysicalField :=
  constantField (HierarchicalLaminates.Material.effectiveOperator b F) + curlField ψ.field -
    coefficientLaw b (constantField F + u.field)

theorem regularMicroscopicResidual_bound (b : PhaseFraction) (F : PhysicalGradient)
    (u ψ : RegularPotential) {εg εj : ℝ}
    (hg : ‖u.field - microscopicGradient b F‖ ≤ εg)
    (hj : ‖curlField ψ.field -
      (microscopicFlux b F - constantField (HierarchicalLaminates.Material.effectiveOperator b F))‖ ≤ εj) :
    ‖regularMicroscopicResidual b F u ψ‖ ≤ εj + εg := by
  have heq : regularMicroscopicResidual b F u ψ =
      (curlField ψ.field -
        (microscopicFlux b F - constantField (HierarchicalLaminates.Material.effectiveOperator b F))) -
      coefficientLaw b (u.field - microscopicGradient b F) := by
    dsimp [regularMicroscopicResidual, microscopicFlux, microscopicGradient]
    simp only [map_sub, map_add]
    abel
  rw [heq]
  exact (norm_sub_le _ _).trans (add_le_add hj ((coefficientLaw_norm_le b _).trans hg))

end HierarchicalLaminates.Composition
