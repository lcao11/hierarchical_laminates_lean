module

public import HierarchicalLaminates.Finite.SymbolProduct

/-!
# Finite expansion of the matrix Neumann recurrence

Expanding the product functional before evaluating the finite sums gives a
scalar formula for the fifth coefficient.
-/

@[expose] public section

namespace HierarchicalLaminates

def prefixedDifferenceQ (P : QMatrix 8 8) (n : ℕ) (k : Frequency) : ℚ :=
  reducedDifferenceQ (P * neumannCoeffQ n k)

theorem finiteLoadingCoefficient_eq_prefixed (n : ℕ) :
    finiteLoadingCoefficient n = prefixedDifferenceQ 1 n (0, 0) := by
  simp only [finiteLoadingCoefficient, prefixedDifferenceQ, one_mul]

theorem prefixedDifferenceQ_zero (P : QMatrix 8 8) (k : Frequency) :
    prefixedDifferenceQ P 0 k = profileCoeffQ k * reducedDifferenceQ P := by
  simp only [prefixedDifferenceQ, neumannCoeffQ, mul_smul_comm, mul_one,
    reducedDifferenceQ_smul]

theorem prefixedDifferenceQ_succ (P : QMatrix 8 8) (n : ℕ) (k : Frequency) :
    prefixedDifferenceQ P (n + 1) k =
      ∑ s : Fin 7, profileWeight s *
        prefixedDifferenceQ (P * directionalSymbolQ (k - profileStep s)) n
          (k - profileStep s) := by
  simp only [prefixedDifferenceQ, neumannCoeffQ, Finset.mul_sum, mul_smul_comm,
    reducedDifferenceQ_sum, reducedDifferenceQ_smul, mul_assoc]

def fastFifthCoefficientQ : ℚ :=
  ∑ s₁ : Fin 7,
    let k₁ := (0, 0) - profileStep s₁
    profileWeight s₁ * (∑ s₂ : Fin 7,
      let k₂ := k₁ - profileStep s₂
      profileWeight s₂ * (∑ s₃ : Fin 7,
        let k₃ := k₂ - profileStep s₃
        profileWeight s₃ * (∑ s₄ : Fin 7,
          let k₄ := k₃ - profileStep s₄
          profileWeight s₄ * (profileCoeffQ k₄ *
            (2 * quarticDetQ (directionalWeightQ k₁) (directionalWeightQ k₂)
              (directionalWeightQ k₃) (directionalWeightQ k₄))))))

theorem fifth_coefficient_eq_fast : finiteLoadingCoefficient 4 = fastFifthCoefficientQ := by
  rw [finiteLoadingCoefficient_eq_prefixed]
  simp only [prefixedDifferenceQ_succ, prefixedDifferenceQ_zero, one_mul,
    difference_symbol_four, fastFifthCoefficientQ]

theorem coefficient_one_zero : finiteLoadingCoefficient 0 = 0 := by
  rw [finiteLoadingCoefficient_eq_prefixed, prefixedDifferenceQ_zero,
    reducedDifferenceQ_identity, mul_zero]

theorem coefficient_two_zero : finiteLoadingCoefficient 1 = 0 := by
  rw [finiteLoadingCoefficient_eq_prefixed]
  simp only [prefixedDifferenceQ_succ, prefixedDifferenceQ_zero, one_mul,
    difference_symbol_one, mul_zero, Finset.sum_const_zero]

theorem coefficient_three_zero : finiteLoadingCoefficient 2 = 0 := by
  rw [finiteLoadingCoefficient_eq_prefixed]
  simp only [prefixedDifferenceQ_succ, prefixedDifferenceQ_zero, one_mul,
    difference_symbol_two, mul_zero, Finset.sum_const_zero]

theorem coefficient_four_zero : finiteLoadingCoefficient 3 = 0 := by
  rw [finiteLoadingCoefficient_eq_prefixed]
  simp only [prefixedDifferenceQ_succ, prefixedDifferenceQ_zero, one_mul,
    difference_symbol_three, mul_zero, Finset.sum_const_zero]

end HierarchicalLaminates
