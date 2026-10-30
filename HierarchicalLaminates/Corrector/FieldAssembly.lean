module

public import HierarchicalLaminates.Corrector.FluxCoefficients

/-!
# Packing scalar L² components into the full physical field
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Corrector

open MeasureTheory HierarchicalLaminates.Periodic

def injectionField (j : PhysicalIndex) : ScalarField →L[ℝ] PhysicalField :=
  (coordinateInjection j).compLpL 2 domainMeasure

lemma component_injectionField (i : Fin 2) (a : Fin 16) (j : PhysicalIndex) (u : ScalarField) :
    componentField i a (injectionField j u) = if (i, a) = j then u else 0 := by
  by_cases hij : (i, a) = j
  · rw [ite_eq_left hij]
    apply Lp.ext
    filter_upwards [(EuclideanSpace.proj (𝕜 := ℝ) (i, a)).coeFn_compLpL (injectionField j u),
      (coordinateInjection j).coeFn_compLpL u] with q hp hi
    change componentField i a (injectionField j u) q = _ at hp
    change injectionField j u q = coordinateInjection j (u q) at hi
    rw [hp, hi]
    change coordinateInjection j (u q) (i, a) = u q
    simp [coordinateInjection_apply, hij]
  · rw [ite_eq_right hij]
    apply Lp.ext
    filter_upwards [(EuclideanSpace.proj (𝕜 := ℝ) (i, a)).coeFn_compLpL (injectionField j u),
      (coordinateInjection j).coeFn_compLpL u, Lp.coeFn_zero ℝ 2 domainMeasure] with q hp hi hz
    change componentField i a (injectionField j u) q = _ at hp
    change injectionField j u q = coordinateInjection j (u q) at hi
    rw [hp, hi, hz]
    change coordinateInjection j (u q) (i, a) = 0
    simp [coordinateInjection_apply, hij]

def assembleField (f : PhysicalIndex → ScalarField) : PhysicalField :=
  ∑ j : PhysicalIndex, injectionField j (f j)

@[simp]
lemma component_assembleField (f : PhysicalIndex → ScalarField) (i : Fin 2) (a : Fin 16) :
    componentField i a (assembleField f) = f (i, a) := by
  simp only [assembleField, map_sum, component_injectionField]
  simp

end HierarchicalLaminates.Corrector
