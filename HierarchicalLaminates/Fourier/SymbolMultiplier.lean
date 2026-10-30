module

public import HierarchicalLaminates.Lamination.DirectionalSymbol
public import HierarchicalLaminates.Fourier.OperatorNorm
public import HierarchicalLaminates.Fourier.ProfileOperators
public import HierarchicalLaminates.Fourier.Neumann
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# The reduced Fourier multiplier and its sequence solution

The coefficient values are real Euclidean operators. Positive-matrix bounds
on the directional symbol control the multiplier and the convergent Neumann
solution.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Fourier

abbrev ReducedSpace := EuclideanSpace ℝ (Fin 8)
abbrev ReducedOperator := ReducedSpace →L[ℝ] ReducedSpace
abbrev ReducedCoefficients := Coefficients HierarchicalLaminates.Frequency ReducedOperator

def realFrequency (k : HierarchicalLaminates.Frequency) : ℝ × ℝ := ((k.1 : ℝ), (k.2 : ℝ))

def reducedSymbolOperator (k : HierarchicalLaminates.Frequency) : ReducedOperator :=
  Matrix.toEuclideanCLM (n := Fin 8) (𝕜 := ℝ)
    (HierarchicalLaminates.Lamination.directionalSymbolR (realFrequency k))

theorem reducedSymbolOperator_norm_le (k : HierarchicalLaminates.Frequency) :
    ‖reducedSymbolOperator k‖ ≤ 3 / 2 :=
  euclidean_norm_le_of_psd_bound (by norm_num)
    (HierarchicalLaminates.Lamination.directionalSymbolR_posSemidef _)
    (HierarchicalLaminates.Lamination.directionalSymbolR_upper_three_halves _)

def coefficientSymbolAction (k : HierarchicalLaminates.Frequency) :
    ReducedOperator →L[ℝ] ReducedOperator :=
  ContinuousLinearMap.compL ℝ ReducedSpace ReducedSpace ReducedSpace (reducedSymbolOperator k)

theorem coefficientSymbolAction_norm_le (k : HierarchicalLaminates.Frequency) (A : ReducedOperator) :
    ‖coefficientSymbolAction k A‖ ≤ (3 / 2 : ℝ) * ‖A‖ := by
  change ‖(reducedSymbolOperator k).comp A‖ ≤ _
  exact ((reducedSymbolOperator k).opNorm_comp_le A).trans
    (mul_le_mul_of_nonneg_right (reducedSymbolOperator_norm_le k) (norm_nonneg A))

def reducedFourierMultiplier : ReducedCoefficients →L[ℝ] ReducedCoefficients :=
  multiplierCLM coefficientSymbolAction (3 / 2) coefficientSymbolAction_norm_le

theorem reducedFourierMultiplier_norm_le (f : ReducedCoefficients) :
    ‖reducedFourierMultiplier f‖ ≤ (3 / 2 : ℝ) * ‖f‖ :=
  multiplierCLM_norm_le _ _ _ f

def contrastIteration (ρ : ℝ) : ReducedCoefficients →L[ℝ] ReducedCoefficients :=
  ρ • profileMultiplication.comp reducedFourierMultiplier

theorem contrastIteration_norm_le {ρ : ℝ} (hρ : 0 ≤ ρ) (f : ReducedCoefficients) :
    ‖contrastIteration ρ f‖ ≤ (3 * ρ / 2) * ‖f‖ := by
  simp only [contrastIteration, smul_apply, ContinuousLinearMap.comp_apply,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ]
  calc
    ρ * ‖profileMultiplication (reducedFourierMultiplier f)‖ ≤
        ρ * ‖reducedFourierMultiplier f‖ :=
      mul_le_mul_of_nonneg_left (profileMultiplication_norm_le _) hρ
    _ ≤ ρ * ((3 / 2 : ℝ) * ‖f‖) :=
      mul_le_mul_of_nonneg_left (reducedFourierMultiplier_norm_le _) hρ
    _ = (3 * ρ / 2) * ‖f‖ := by ring

def profileSource : ReducedCoefficients :=
  profileMultiplication (lp.single 1 (0, 0) (ContinuousLinearMap.id ℝ ReducedSpace))

theorem profileSource_norm_le : ‖profileSource‖ ≤ 1 := by
  refine (profileMultiplication_norm_le _).trans ?_
  simpa only [lp.norm_single (by norm_num : (0 : ENNReal) < 1)] using
    (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := ReducedSpace))

def rhoSource : ReducedCoefficients := HierarchicalLaminates.rho • profileSource

theorem rhoSource_norm_le : ‖rhoSource‖ ≤ HierarchicalLaminates.rho := by
  rw [rhoSource, norm_smul, Real.norm_eq_abs, abs_of_nonneg HierarchicalLaminates.rho_pos.le]
  exact mul_le_of_le_one_right HierarchicalLaminates.rho_pos.le profileSource_norm_le

def rhoSolution : ReducedCoefficients := neumannSolution (contrastIteration HierarchicalLaminates.rho) rhoSource

theorem rhoContraction_nonneg : 0 ≤ 3 * HierarchicalLaminates.rho / 2 := by
  linarith [HierarchicalLaminates.rho_pos]

theorem rhoSolution_equation : rhoSolution = rhoSource + contrastIteration HierarchicalLaminates.rho rhoSolution := by
  exact neumannSolution_equation _ rhoContraction_nonneg HierarchicalLaminates.contraction_lt_one
    (contrastIteration_norm_le HierarchicalLaminates.rho_pos.le) _

theorem rhoSolution_tail (N : ℕ) :
    ‖rhoSolution - ∑ n ∈ Finset.range N, neumannTerm (contrastIteration HierarchicalLaminates.rho) rhoSource n‖ ≤
      HierarchicalLaminates.rho * (3 * HierarchicalLaminates.rho / 2) ^ N / (1 - 3 * HierarchicalLaminates.rho / 2) := by
  have ht := neumannSolution_tail (contrastIteration HierarchicalLaminates.rho) rhoContraction_nonneg
    HierarchicalLaminates.contraction_lt_one (contrastIteration_norm_le HierarchicalLaminates.rho_pos.le) rhoSource N
  refine ht.trans ?_
  apply div_le_div_of_nonneg_right _ HierarchicalLaminates.contraction_pos.le
  exact mul_le_mul_of_nonneg_right rhoSource_norm_le (pow_nonneg rhoContraction_nonneg N)

theorem rhoSolution_tail_five :
    ‖rhoSolution - ∑ n ∈ Finset.range 5, neumannTerm (contrastIteration HierarchicalLaminates.rho) rhoSource n‖ ≤
      (3 / 2 : ℝ) ^ 5 * HierarchicalLaminates.rho ^ 6 / (1 - 3 * HierarchicalLaminates.rho / 2) := by
  convert rhoSolution_tail 5 using 1; ring

end HierarchicalLaminates.Fourier
