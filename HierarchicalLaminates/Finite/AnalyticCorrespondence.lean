module

public import HierarchicalLaminates.Finite.RealTransfer
public import HierarchicalLaminates.Fourier.SymbolMultiplier

/-!
# The finite recurrence and the convergent coefficient solution

The finite matrix recurrence agrees pointwise with the recurrence for the
convergent coefficient-space response.
-/

@[expose] public section

namespace HierarchicalLaminates

noncomputable section

open Fourier

def matrixOperatorQ (A : QMatrix 8 8) : ReducedOperator :=
  Matrix.toEuclideanCLM (n := Fin 8) (𝕜 := ℝ) (realMatrix A)

theorem matrixOperatorQ_one : matrixOperatorQ (1 : QMatrix 8 8) =
    ContinuousLinearMap.id ℝ ReducedSpace := by
  unfold matrixOperatorQ
  rw [realMatrix_one, map_one]
  rfl

theorem matrixOperatorQ_smul (a : ℚ) (A : QMatrix 8 8) :
    matrixOperatorQ (a • A) = (a : ℝ) • matrixOperatorQ A := by
  simp [matrixOperatorQ, realMatrix_smul, map_smul]

theorem matrixOperatorQ_mul (A B : QMatrix 8 8) :
    matrixOperatorQ (A * B) = (matrixOperatorQ A).comp (matrixOperatorQ B) := by
  unfold matrixOperatorQ
  rw [realMatrix_mul, map_mul]
  rfl

theorem matrixOperatorQ_sum {ι : Type*} (s : Finset ι) (f : ι → QMatrix 8 8) :
    matrixOperatorQ (∑ i ∈ s, f i) = ∑ i ∈ s, matrixOperatorQ (f i) := by
  unfold matrixOperatorQ
  rw [realMatrix_finite_sum, map_sum]

theorem directionalSymbolQ_operator (k : Frequency) :
    matrixOperatorQ (directionalSymbolQ k) = reducedSymbolOperator k := by
  unfold matrixOperatorQ reducedSymbolOperator
  rw [directionalSymbolQ_cast]
  rfl

theorem profileCoeffQ_zero_of_not_step (k : Frequency)
    (hk : ∀ s : Fin 7, k ≠ profileStep s) : profileCoeffQ k = 0 := by
  have h0 : k ≠ (0, 0) := hk 0
  have h1 : k ≠ (1, 0) := hk 1
  have h2 : k ≠ (-1, 0) := hk 2
  have h3 : k ≠ (0, 1) := hk 3
  have h4 : k ≠ (0, -1) := hk 4
  have h5 : k ≠ (1, 3) := hk 5
  have h6 : k ≠ (-1, -3) := hk 6
  simp [profileCoeffQ, h0, h1, h2, h3, h4, h5, h6]

theorem frequency_sub_eq_zero_iff (k l : Frequency) :
    k - l = (0, 0) ↔ k = l := by
  change k - l = (0 : Frequency) ↔ k = l
  exact sub_eq_zero

theorem profileSource_at_step (s : Fin 7) :
    profileSource (profileStep s) =
      (profileWeight s : ℝ) • ContinuousLinearMap.id ℝ ReducedSpace := by
  rw [profileSource, profileMultiplication_apply]
  simp only [lp.single_apply, Pi.single_apply]
  simp_rw [frequency_sub_eq_zero_iff]
  have heq (j : Fin 7) : profileStep s = profileStep j ↔ j = s := by
    constructor
    · intro h
      exact (profile_steps_distinct h).symm
    · intro h
      simp only [h]
  simp [heq, smul_ite, realProfileWeight]

theorem profileSource_apply (k : Frequency) :
    profileSource k = (profileCoeffQ k : ℝ) • ContinuousLinearMap.id ℝ ReducedSpace := by
  by_cases hk : ∃ s : Fin 7, k = profileStep s
  · obtain ⟨s, rfl⟩ := hk
    rw [profileSource_at_step, profile_coeff_at_step]
  · have hnone : ∀ s : Fin 7, k ≠ profileStep s := by
      simpa only [not_exists] using hk
    rw [profileCoeffQ_zero_of_not_step k hnone]
    rw [profileSource, profileMultiplication_apply]
    simp only [lp.single_apply, Pi.single_apply]
    simp_rw [frequency_sub_eq_zero_iff]
    simp [hnone]
    change (0 : ReducedOperator) = (0 : ℝ) • ContinuousLinearMap.id ℝ ReducedSpace
    exact (zero_smul ℝ (ContinuousLinearMap.id ℝ ReducedSpace)).symm

def profileIteration : ReducedCoefficients →L[ℝ] ReducedCoefficients :=
  profileMultiplication.comp reducedFourierMultiplier

theorem profileIteration_apply (f : ReducedCoefficients) (k : Frequency) :
    profileIteration f k = ∑ s : Fin 7, realProfileWeight s •
      (reducedSymbolOperator (k - profileStep s)).comp (f (k - profileStep s)) := by
  simp only [profileIteration, ContinuousLinearMap.comp_apply, profileMultiplication_apply,
    reducedFourierMultiplier, multiplierCLM_apply, coefficientSymbolAction,
    ContinuousLinearMap.compL_apply]

theorem unscaledTerm_eq_matrixOperator (n : ℕ) (k : Frequency) :
    neumannTerm profileIteration profileSource n k = matrixOperatorQ (neumannCoeffQ n k) := by
  induction n generalizing k with
  | zero =>
      simp only [neumannTerm_zero, profileSource_apply, neumannCoeffQ,
        matrixOperatorQ_smul, matrixOperatorQ_one]
  | succ n ih =>
      rw [neumannTerm_succ, profileIteration_apply]
      simp only [neumannCoeffQ, matrixOperatorQ_sum, matrixOperatorQ_smul,
        matrixOperatorQ_mul, directionalSymbolQ_operator]
      apply Finset.sum_congr rfl
      intro s _
      rw [ih]
      rfl

theorem neumannTerm_scale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E) (f : E) (r : ℝ) (n : ℕ) :
    neumannTerm (r • A) (r • f) n = r ^ (n + 1) • neumannTerm A f n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [neumannTerm_succ, ih, smul_apply, map_smul,
        smul_smul, neumannTerm_succ]
      congr 1
      ring

theorem rhoTerm_eq_matrixOperator (n : ℕ) (k : Frequency) :
    neumannTerm (contrastIteration rho) rhoSource n k =
      rho ^ (n + 1) • matrixOperatorQ (neumannCoeffQ n k) := by
  change neumannTerm (rho • profileIteration) (rho • profileSource) n k = _
  rw [neumannTerm_scale]
  change rho ^ (n + 1) • neumannTerm profileIteration profileSource n k = _
  rw [unscaledTerm_eq_matrixOperator]

end
end HierarchicalLaminates
