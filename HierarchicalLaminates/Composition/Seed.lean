module

public import HierarchicalLaminates.Composition.Interfaces

/-!
# A half-fraction seed for all prescribed fractions
-/

@[expose] public section
noncomputable section

namespace HierarchicalLaminates.Composition

open MeasureTheory HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material
  HierarchicalLaminates.Lamination HierarchicalLaminates.Homogenization

def seedCount : ℕ := Classical.choose half_fraction_counterexample

theorem seedCount_ge_two : 2 ≤ seedCount :=
  (Classical.choose_spec half_fraction_counterexample).1

def seedFraction : PhaseFraction := binaryFraction seedCount

theorem seedFraction_binary : IsBinary seedFraction :=
  (Classical.choose_spec half_fraction_counterexample).2.1

theorem seedFraction_mean : phaseMean seedFraction = 1 / 2 :=
  (Classical.choose_spec half_fraction_counterexample).2.2.1

theorem seedFraction_cell_energy (F : PhysicalGradient) :
    quadraticEnergy (effectiveMatrix seedFraction) (F : Fin 2 × Fin 16 → ℝ) =
      sobolevCellEnergy (coefficientLaw seedFraction) F :=
  (Classical.choose_spec half_fraction_counterexample).2.2.2.1 F

theorem seedFraction_positive : 0 < physicalLoadingDifference seedFraction :=
  (Classical.choose_spec half_fraction_counterexample).2.2.2.2.1

theorem seedFraction_mem_GClosure : effectiveMatrix seedFraction ∈ GClosure (1 / 2) := by
  rw [← seedFraction_mean]
  exact effectiveMatrix_mem_GClosure seedFraction_binary

theorem candidate_positive {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    0 < loadingDifference xiFlat etaFlat (arithmeticCandidate θ (effectiveMatrix seedFraction)) :=
  arithmeticCandidate_positive hθ₀ hθ₁ seedFraction_positive

theorem half_candidate_mem_GClosure :
    arithmeticCandidate (1 / 2) (effectiveMatrix seedFraction) ∈ GClosure (1 / 2) := by
  have ha : layerFraction (1 / 2) = 1 := (layerFraction_eq_one_iff _).2 rfl
  unfold arithmeticCandidate
  rw [ha]
  simpa [matrixAverage] using seedFraction_mem_GClosure

end HierarchicalLaminates.Composition
