module

public import HierarchicalLaminates.Finite.Coefficients
public import HierarchicalLaminates.Algebra.RealData
public import HierarchicalLaminates.Lamination.DirectionalSymbol

/-! Exact transfer of the rational Fourier symbol to its physical real version. -/

@[expose] public section

namespace HierarchicalLaminates

noncomputable section

def integerFrequencyR (k : Frequency) : ℝ × ℝ := ((k.1 : ℝ), (k.2 : ℝ))

theorem directionalWeightQ_cast (k : Frequency) (j : Fin 4) :
    (directionalWeightQ k j : ℝ) =
      Lamination.directionalWeightR (integerFrequencyR k) j := by
  by_cases hk : k = (0, 0)
  · subst k
    simp [directionalWeightQ, integerFrequencyR, Lamination.directionalWeightR,
      Lamination.directionalDegreeR]
  · simp [directionalWeightQ, hk, integerFrequencyR, Lamination.directionalWeightR,
      Lamination.directionalDegreeR, Nat.cast_add, Nat.cast_one]

theorem realMatrix_finite_sum {ι : Type*} (s : Finset ι) (f : ι → QMatrix 8 8) :
    realMatrix (∑ i ∈ s, f i) = ∑ i ∈ s, realMatrix (f i) := by
  ext i j
  simp [realMatrix, Matrix.sum_apply, map_sum]

theorem directionalSymbolQ_cast (k : Frequency) :
    realMatrix (directionalSymbolQ k) =
      Lamination.directionalSymbolR (integerFrequencyR k) := by
  unfold directionalSymbolQ Lamination.directionalSymbolR
  rw [realMatrix_finite_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [realMatrix_smul, realMatrix_add, realMatrix_one, directionalWeightQ_cast]
  rfl

theorem reducedDifferenceQ_cast (M : QMatrix 8 8) :
    (reducedDifferenceQ M : ℝ) = reducedDifferenceR (realMatrix M) := by
  simp [reducedDifferenceQ, reducedDifferenceR, realMatrix]

theorem real_coefficient_one :
    reducedDifferenceR (realMatrix (neumannCoeffQ 0 (0, 0))) = 0 := by
  rw [← reducedDifferenceQ_cast]
  exact_mod_cast loading_coefficient_one

theorem real_coefficient_two :
    reducedDifferenceR (realMatrix (neumannCoeffQ 1 (0, 0))) = 0 := by
  rw [← reducedDifferenceQ_cast]
  exact_mod_cast loading_coefficient_two

theorem real_coefficient_three :
    reducedDifferenceR (realMatrix (neumannCoeffQ 2 (0, 0))) = 0 := by
  rw [← reducedDifferenceQ_cast]
  exact_mod_cast loading_coefficient_three

theorem real_coefficient_four :
    reducedDifferenceR (realMatrix (neumannCoeffQ 3 (0, 0))) = 0 := by
  rw [← reducedDifferenceQ_cast]
  exact_mod_cast loading_coefficient_four

theorem real_coefficient_five :
    reducedDifferenceR (realMatrix (neumannCoeffQ 4 (0, 0))) = 2 * kappa := by
  rw [← reducedDifferenceQ_cast]
  change ((finiteLoadingCoefficient 4 : ℚ) : ℝ) = 2 * (kappaQ : ℝ)
  exact_mod_cast loading_coefficient_five

end
end HierarchicalLaminates
