module

public import HierarchicalLaminates.Finite.Profile
public import HierarchicalLaminates.Finite.ProductRule
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FinCases

/-! Exact scalar product formulas for the same rational directional symbol. -/

@[expose] public section

namespace HierarchicalLaminates

def symbolCoordinatesQ (k : Frequency) : Fin 5 → ℚ :=
  ![∑ j : Fin 4, directionalWeightQ k j,
    directionalWeightQ k 0, directionalWeightQ k 1,
    directionalWeightQ k 2, directionalWeightQ k 3]

theorem symbolCoordinatesQ_succ (k : Frequency) (j : Fin 4) :
    symbolCoordinatesQ k j.succ = directionalWeightQ k j := by
  fin_cases j <;> rfl

theorem directionalSymbolQ_eq_spin (k : Frequency) :
    directionalSymbolQ k = spinCombinationQ (symbolCoordinatesQ k) := by
  simp [directionalSymbolQ, spinCombinationQ, symbolCoordinatesQ,
    cliffordBasisQ, Fin.sum_univ_succ, smul_add, add_smul]
  abel

def scalarCoordinatesQ : Fin 5 → ℚ := ![1, 0, 0, 0, 0]

theorem spinCombinationQ_scalar : spinCombinationQ scalarCoordinatesQ = 1 := by
  decide +kernel

theorem difference_spin_three (a b c : Fin 5 → ℚ) :
    reducedDifferenceQ (spinCombinationQ a * spinCombinationQ b * spinCombinationQ c) = 0 := by
  have h := difference_spin_four a b c scalarCoordinatesQ
  rw [spinCombinationQ_scalar, mul_one] at h
  simpa [scalarCoordinatesQ, quarticDetQ] using h

theorem difference_spin_two (a b : Fin 5 → ℚ) :
    reducedDifferenceQ (spinCombinationQ a * spinCombinationQ b) = 0 := by
  have h := difference_spin_three a b scalarCoordinatesQ
  simpa only [spinCombinationQ_scalar, mul_one] using h

theorem difference_spin_one (a : Fin 5 → ℚ) :
    reducedDifferenceQ (spinCombinationQ a) = 0 := by
  have h := difference_spin_two a scalarCoordinatesQ
  simpa only [spinCombinationQ_scalar, mul_one] using h

theorem difference_symbol_one (a : Frequency) :
    reducedDifferenceQ (directionalSymbolQ a) = 0 := by
  rw [directionalSymbolQ_eq_spin]
  exact difference_spin_one _

theorem difference_symbol_two (a b : Frequency) :
    reducedDifferenceQ (directionalSymbolQ a * directionalSymbolQ b) = 0 := by
  rw [directionalSymbolQ_eq_spin, directionalSymbolQ_eq_spin]
  exact difference_spin_two _ _

theorem difference_symbol_three (a b c : Frequency) :
    reducedDifferenceQ (directionalSymbolQ a * directionalSymbolQ b * directionalSymbolQ c) = 0 := by
  rw [directionalSymbolQ_eq_spin, directionalSymbolQ_eq_spin, directionalSymbolQ_eq_spin]
  exact difference_spin_three _ _ _

theorem difference_symbol_four (a b c d : Frequency) :
    reducedDifferenceQ (directionalSymbolQ a * directionalSymbolQ b *
      directionalSymbolQ c * directionalSymbolQ d) =
      2 * quarticDetQ (directionalWeightQ a) (directionalWeightQ b)
        (directionalWeightQ c) (directionalWeightQ d) := by
  rw [directionalSymbolQ_eq_spin, directionalSymbolQ_eq_spin,
    directionalSymbolQ_eq_spin, directionalSymbolQ_eq_spin]
  simpa only [symbolCoordinatesQ_succ] using
    difference_spin_four (symbolCoordinatesQ a) (symbolCoordinatesQ b)
      (symbolCoordinatesQ c) (symbolCoordinatesQ d)

end HierarchicalLaminates
