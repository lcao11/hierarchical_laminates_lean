module

public import HierarchicalLaminates.Material.Selection
public import HierarchicalLaminates.Corrector.BinaryResidual

/-! The two selected physical binary energies converge with a finite error rate. -/

@[expose] public section
noncomputable section

namespace HierarchicalLaminates.Material

open HierarchicalLaminates.Periodic HierarchicalLaminates.Corrector HierarchicalLaminates.Lamination

abbrev plusPotential : PotentialVector := WithLp.toLp 2 loadPlusR
abbrev minusPotential : PotentialVector := WithLp.toLp 2 loadMinusR

def horizontalCellEnergy (b : PhaseFraction) (z : PotentialVector) : ℝ :=
  inner ℝ (effectiveOperator b (horizontalLoading z)) (horizontalLoading z)

theorem physicalLoadingDifference_eq_energies (b : PhaseFraction) :
    physicalLoadingDifference b = horizontalCellEnergy b minusPotential -
      horizontalCellEnergy b plusPotential := by
  have he (F : PhysicalGradient) :
      quadraticEnergy (effectiveMatrix b) (F : Fin 2 × Fin 16 → ℝ) =
        inner ℝ (effectiveOperator b F) F :=
    (effectiveMatrix_quadratic_energy b F).trans (effectiveOperator_cell_energy b F).symm
  have hp := he (horizontalLoading plusPotential)
  have hm := he (horizontalLoading minusPotential)
  rw [horizontalLoading_plus] at hp
  rw [horizontalLoading_minus] at hm
  unfold horizontalCellEnergy
  rw [horizontalLoading_minus, horizontalLoading_plus]
  exact congrArg₂ (· - ·) hm hp

def binaryEnergyRate (z : PotentialVector) : ℝ :=
  5 * ‖horizontalLoading z‖ * binaryResidualRate z

theorem binary_energy_error (N : ℕ) (hN : 0 < N) (z : PotentialVector) :
    |horizontalCellEnergy (binaryFraction N) z - horizontalCellEnergy smoothFraction z| ≤
      binaryEnergyRate z / (N : ℝ) := by
  have h := mul_le_mul_of_nonneg_left (binaryResidual_norm_le N hN z)
    (by positivity : 0 ≤ 5 * ‖horizontalLoading z‖)
  refine (binaryLoadingEnergy_error N hN z).trans ?_
  convert h using 1
  unfold binaryEnergyRate
  ring

def binaryGapRate : ℝ := binaryEnergyRate minusPotential + binaryEnergyRate plusPotential

theorem binary_physical_gap_error (N : ℕ) (hN : 0 < N) :
    |physicalLoadingDifference (binaryFraction N) - physicalLoadingDifference smoothFraction| ≤
      binaryGapRate / (N : ℝ) := by
  rw [physicalLoadingDifference_eq_energies, physicalLoadingDifference_eq_energies]
  calc
    _ = |(horizontalCellEnergy (binaryFraction N) minusPotential -
          horizontalCellEnergy smoothFraction minusPotential) -
        (horizontalCellEnergy (binaryFraction N) plusPotential -
          horizontalCellEnergy smoothFraction plusPotential)| := by congr 1; ring
    _ ≤ |horizontalCellEnergy (binaryFraction N) minusPotential -
          horizontalCellEnergy smoothFraction minusPotential| +
        |horizontalCellEnergy (binaryFraction N) plusPotential -
          horizontalCellEnergy smoothFraction plusPotential| := abs_sub _ _
    _ ≤ binaryEnergyRate minusPotential / (N : ℝ) +
        binaryEnergyRate plusPotential / (N : ℝ) :=
      add_le_add (binary_energy_error N hN minusPotential) (binary_energy_error N hN plusPotential)
    _ = binaryGapRate / (N : ℝ) := by rw [← add_div]; rfl

end HierarchicalLaminates.Material
