module

public import HierarchicalLaminates.Finite.Profile
public import HierarchicalLaminates.Fourier.SequenceOperators

/-!
# The seven-shift profile operator

The seven rational Fourier weights act on coefficient sequences by a finite
sum of frequency shifts.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Fourier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def realProfileWeight (s : Fin 7) : ℝ := (HierarchicalLaminates.profileWeight s : ℝ)

theorem realProfileWeight_mass : (∑ s : Fin 7, |realProfileWeight s|) = 1 := by
  norm_num [realProfileWeight, HierarchicalLaminates.profileWeight, Fin.sum_univ_succ]

def profileMultiplication :
    Coefficients HierarchicalLaminates.Frequency E →L[ℝ] Coefficients HierarchicalLaminates.Frequency E :=
  weightedShifts HierarchicalLaminates.profileStep realProfileWeight

theorem profileMultiplication_norm_le (f : Coefficients HierarchicalLaminates.Frequency E) :
    ‖profileMultiplication f‖ ≤ ‖f‖ := by
  exact weightedShifts_norm_le_one HierarchicalLaminates.profileStep realProfileWeight
    (le_of_eq realProfileWeight_mass) f

@[simp]
theorem profileMultiplication_apply (f : Coefficients HierarchicalLaminates.Frequency E)
    (k : HierarchicalLaminates.Frequency) :
    profileMultiplication f k =
      ∑ s : Fin 7, realProfileWeight s • f (k - HierarchicalLaminates.profileStep s) := by
  simp only [profileMultiplication, weightedShifts, sum_apply, smul_apply]
  change (lp.evalₗ (𝕜 := ℝ) (fun _ : HierarchicalLaminates.Frequency => E) 1 k)
    (∑ s : Fin 7, realProfileWeight s • shift (HierarchicalLaminates.profileStep s) f) = _
  rw [map_sum]
  simp only [map_smul, lp.evalₗ_apply, shift_apply]

end HierarchicalLaminates.Fourier
