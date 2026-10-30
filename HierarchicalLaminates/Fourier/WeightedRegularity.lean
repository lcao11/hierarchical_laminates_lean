module

public import HierarchicalLaminates.Fourier.Differentiation
public import HierarchicalLaminates.Fourier.Response
public import Mathlib.Tactic.Linarith

/-!
# Polynomial frequency regularity of the infinite response

Each Neumann step shifts frequencies by at most one horizontally and three
vertically. Polynomial weights therefore give a polynomial times geometric
bound. Summing in ℓ¹ yields the derivative coefficients of the continuous
response.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Fourier

def frequencyBox (n : ℕ) (k : HierarchicalLaminates.Frequency) : Prop :=
  |k.1| ≤ (n : ℤ) ∧ |k.2| ≤ 3 * (n : ℤ)

theorem profileStep_frequencyBox (s : Fin 7) : frequencyBox 1 (HierarchicalLaminates.profileStep s) := by
  fin_cases s <;> norm_num [frequencyBox, HierarchicalLaminates.profileStep]

theorem frequencyBox_of_sub {n : ℕ} {k v : HierarchicalLaminates.Frequency}
    (hk : frequencyBox n (k - v)) (hv : frequencyBox 1 v) : frequencyBox (n + 1) k := by
  have hx : |k.1| ≤ |k.1 - v.1| + |v.1| := by
    simpa using abs_add_le (k.1 - v.1) v.1
  have hy : |k.2| ≤ |k.2 - v.2| + |v.2| := by
    simpa using abs_add_le (k.2 - v.2) v.2
  change |k.1 - v.1| ≤ (n : ℤ) ∧ |k.2 - v.2| ≤ 3 * (n : ℤ) at hk
  simp only [frequencyBox, Nat.cast_add, Nat.cast_one] at *
  rcases hk with ⟨hkx, hky⟩
  rcases hv with ⟨hvx, hvy⟩
  constructor <;> linarith

theorem profileMultiplication_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (f : Coefficients HierarchicalLaminates.Frequency E)
    (hf : ∀ k, ¬frequencyBox n k → f k = 0) :
    ∀ k, ¬frequencyBox (n + 1) k → profileMultiplication f k = 0 := by
  intro k hk
  rw [profileMultiplication_apply]
  apply Finset.sum_eq_zero
  intro s _
  rw [hf (k - HierarchicalLaminates.profileStep s) (fun h =>
    hk (frequencyBox_of_sub h (profileStep_frequencyBox s)))]
  exact smul_zero _

abbrev rhoTerm (n : ℕ) : ReducedCoefficients :=
  neumannTerm (contrastIteration HierarchicalLaminates.rho) rhoSource n

theorem reducedOperator_smul_zero (c : ℝ) : c • (0 : ReducedOperator) = 0 := by
  ext v j
  simp

theorem rhoSource_support : ∀ k, ¬frequencyBox 1 k → rhoSource k = 0 := by
  have hdelta : ∀ k, ¬frequencyBox 0 k →
      (lp.single 1 (0, 0) (ContinuousLinearMap.id ℝ ReducedSpace) : ReducedCoefficients) k = 0 := by
    intro k hk
    apply lp.single_apply_ne
    intro heq
    subst k
    exact hk (by norm_num [frequencyBox])
  intro k hk
  change HierarchicalLaminates.rho • profileMultiplication
    (lp.single 1 (0, 0) (ContinuousLinearMap.id ℝ ReducedSpace)) k = 0
  rw [profileMultiplication_support 0 _ hdelta k hk]
  exact reducedOperator_smul_zero HierarchicalLaminates.rho

theorem rhoTerm_support (n : ℕ) : ∀ k, ¬frequencyBox (n + 1) k → rhoTerm n k = 0 := by
  induction n with
  | zero => exact rhoSource_support
  | succ n ih =>
      intro k hk
      have hmult : ∀ l, ¬frequencyBox (n + 1) l → reducedFourierMultiplier (rhoTerm n) l = 0 := by
        intro l hl
        simp only [reducedFourierMultiplier, multiplierCLM_apply, ih l hl, map_zero]
      change HierarchicalLaminates.rho • profileMultiplication (reducedFourierMultiplier (rhoTerm n)) k = 0
      rw [profileMultiplication_support (n + 1) _ hmult k hk]
      exact reducedOperator_smul_zero HierarchicalLaminates.rho

theorem rhoTerm_norm_le (n : ℕ) : ‖rhoTerm n‖ ≤
    HierarchicalLaminates.rho * (3 * HierarchicalLaminates.rho / 2) ^ n := by
  exact (neumannTerm_norm_le _ rhoContraction_nonneg
    (contrastIteration_norm_le HierarchicalLaminates.rho_pos.le) rhoSource n).trans
      (mul_le_mul_of_nonneg_right rhoSource_norm_le (pow_nonneg rhoContraction_nonneg n))

theorem frequencyBox_coordinate_bound {n : ℕ} {k : HierarchicalLaminates.Frequency}
    (hk : frequencyBox n k) (i : Fin 2) : |(frequencyVector k i : ℝ)| ≤ 3 * (n : ℝ) := by
  fin_cases i
  · have hx : |(k.1 : ℝ)| ≤ (n : ℝ) := by exact_mod_cast hk.1
    have hn : (n : ℝ) ≤ 3 * (n : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    simpa [frequencyVector] using hx.trans hn
  · have hy : |(k.2 : ℝ)| ≤ 3 * (n : ℝ) := by exact_mod_cast hk.2
    simpa [frequencyVector] using hy

theorem weightedRhoTerm_pointwise_bound (d : ℕ) (i : Fin 2) (n : ℕ)
    (k : HierarchicalLaminates.Frequency) :
    ‖(frequencyVector k i : ℝ) ^ d • rhoTerm n k‖ ≤
      (3 * ((n : ℝ) + 1)) ^ d * ‖rhoTerm n k‖ := by
  by_cases hk : frequencyBox (n + 1) k
  · rw [norm_smul, Real.norm_eq_abs, abs_pow]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply pow_le_pow_left₀ (abs_nonneg _)
    simpa only [Nat.cast_add, Nat.cast_one] using frequencyBox_coordinate_bound hk i
  · rw [rhoTerm_support n k hk]
    have hz := reducedOperator_smul_zero ((frequencyVector k i : ℝ) ^ d)
    rw [hz, norm_zero, mul_zero]

def weightedRhoTerm (d : ℕ) (i : Fin 2) (n : ℕ) : ReducedCoefficients :=
  ⟨fun k => (frequencyVector k i : ℝ) ^ d • rhoTerm n k, by
    apply memℓp_gen
    have hs := (coefficients_summable_norm (rhoTerm n)).mul_left ((3 * ((n : ℝ) + 1)) ^ d)
    have hn := hs.of_nonneg_of_le (fun _ => norm_nonneg _) (weightedRhoTerm_pointwise_bound d i n)
    simpa only [ENNReal.toReal_one, Real.rpow_one] using hn⟩

@[simp]
theorem weightedRhoTerm_apply (d : ℕ) (i : Fin 2) (n : ℕ) (k : HierarchicalLaminates.Frequency) :
    weightedRhoTerm d i n k = (frequencyVector k i : ℝ) ^ d • rhoTerm n k := rfl

theorem weightedRhoTerm_norm_le (d : ℕ) (i : Fin 2) (n : ℕ) :
    ‖weightedRhoTerm d i n‖ ≤ (3 * ((n : ℝ) + 1)) ^ d *
      (HierarchicalLaminates.rho * (3 * HierarchicalLaminates.rho / 2) ^ n) := by
  calc
    ‖weightedRhoTerm d i n‖ ≤ (3 * ((n : ℝ) + 1)) ^ d * ‖rhoTerm n‖ := by
      rw [coefficients_norm_eq, coefficients_norm_eq]
      have hs := (coefficients_summable_norm (rhoTerm n)).mul_left ((3 * ((n : ℝ) + 1)) ^ d)
      exact ((coefficients_summable_norm (weightedRhoTerm d i n)).tsum_le_tsum
        (weightedRhoTerm_pointwise_bound d i n) hs).trans_eq tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (rhoTerm_norm_le n) (by positivity)

theorem summable_polynomial_neumann_bound (d : ℕ) :
    Summable (fun n : ℕ => (3 * ((n : ℝ) + 1)) ^ d *
      (HierarchicalLaminates.rho * (3 * HierarchicalLaminates.rho / 2) ^ n)) := by
  let q : ℝ := 3 * HierarchicalLaminates.rho / 2
  have hqpos : 0 < q := by dsimp [q]; nlinarith [HierarchicalLaminates.rho_pos]
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hqpos]
    exact HierarchicalLaminates.contraction_lt_one
  have hs := summable_pow_mul_geometric_of_norm_lt_one d hqnorm
  have hshift := (summable_nat_add_iff 1).mpr hs
  have hscaled := hshift.mul_left ((3 : ℝ) ^ d * HierarchicalLaminates.rho / q)
  convert hscaled using 1
  funext n
  simp only [Nat.cast_add, Nat.cast_one, pow_succ]
  dsimp [q]
  rw [mul_pow]
  field_simp [ne_of_gt HierarchicalLaminates.rho_pos]

theorem weightedRhoTerm_summable (d : ℕ) (i : Fin 2) :
    Summable (weightedRhoTerm d i) :=
  (summable_polynomial_neumann_bound d).of_norm_bounded (weightedRhoTerm_norm_le d i)

def polynomialFrequencyCoefficients (d : ℕ) (i : Fin 2) : ReducedCoefficients :=
  ∑' n, weightedRhoTerm d i n

theorem polynomialFrequencyCoefficients_apply (d : ℕ) (i : Fin 2)
    (k : HierarchicalLaminates.Frequency) :
    polynomialFrequencyCoefficients d i k =
      (frequencyVector k i : ℝ) ^ d • rhoSolution k := by
  have hs : Summable rhoTerm := neumannTerm_summable _ rhoContraction_nonneg
    HierarchicalLaminates.contraction_lt_one (contrastIteration_norm_le HierarchicalLaminates.rho_pos.le) rhoSource
  have hEval := (lp.evalCLM ℝ (fun _ : HierarchicalLaminates.Frequency => ReducedOperator) 1 k).map_tsum
    (weightedRhoTerm_summable d i)
  have hEvalBase := (lp.evalCLM ℝ (fun _ : HierarchicalLaminates.Frequency => ReducedOperator) 1 k).map_tsum hs
  change polynomialFrequencyCoefficients d i k = ∑' n, weightedRhoTerm d i n k at hEval
  change rhoSolution k = ∑' n, rhoTerm n k at hEvalBase
  rw [hEval, hEvalBase]
  simp only [weightedRhoTerm_apply]
  have hsp : Summable (fun n => rhoTerm n k) :=
    (lp.evalCLM ℝ (fun _ : HierarchicalLaminates.Frequency => ReducedOperator) 1 k).summable hs
  exact hsp.tsum_const_smul ((frequencyVector k i : ℝ) ^ d)

theorem rhoSolution_polynomial_frequency_summable (d : ℕ) (i : Fin 2) :
    Summable (fun k : HierarchicalLaminates.Frequency =>
      ‖(frequencyVector k i : ℝ) ^ d • rhoSolution k‖) := by
  simpa only [polynomialFrequencyCoefficients_apply] using
    coefficients_summable_norm (polynomialFrequencyCoefficients d i)

theorem rhoSolution_frequency_moment_summable (d : ℕ) (i : Fin 2) :
    Summable (fun k : HierarchicalLaminates.Frequency =>
      |(frequencyVector k i : ℝ)| ^ d * ‖rhoSolution k‖) := by
  simpa only [norm_smul, Real.norm_eq_abs, abs_pow] using
    rhoSolution_polynomial_frequency_summable d i

def responseDerivativeCoefficients (i : Fin 2) : ReducedCoefficients :=
  -(2 * Real.pi) • polynomialFrequencyCoefficients 1 i

theorem responseDerivativeCoefficients_apply (i : Fin 2) (k : HierarchicalLaminates.Frequency) :
    responseDerivativeCoefficients i k = -(angularFrequency k i) • rhoSolution k := by
  change (-(2 * Real.pi)) • polynomialFrequencyCoefficients 1 i k = _
  rw [polynomialFrequencyCoefficients_apply]
  simp only [pow_one, smul_smul, angularFrequency, neg_mul]

def reducedResponseDerivative (i : Fin 2) : C(PeriodicDomain, ReducedOperator) :=
  sineSynthesis (responseDerivativeCoefficients i)

theorem reducedResponse_hasDerivAt_flow (i : Fin 2) (q : PeriodicDomain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => reducedResponse (HierarchicalLaminates.Periodic.coordinateFlow i q s))
      (reducedResponseDerivative i (HierarchicalLaminates.Periodic.coordinateFlow i q t)) t :=
  hasDerivAt_cosineSynthesis_flow rhoSolution (responseDerivativeCoefficients i) i
    (fun k => responseDerivativeCoefficients_apply i k) q t

theorem reducedResponseDerivative_bounded (i : Fin 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q, ‖reducedResponseDerivative i q‖ ≤ C :=
  ⟨‖reducedResponseDerivative i‖, norm_nonneg (reducedResponseDerivative i),
    (reducedResponseDerivative i).norm_coe_le_norm⟩

/-- The synthesized multiplier response used by the physical amplitude σ. -/
def multiplierResponse : C(PeriodicDomain, ReducedOperator) :=
  cosineSynthesis (reducedFourierMultiplier rhoSolution)

def multiplierResponseDerivative (i : Fin 2) : C(PeriodicDomain, ReducedOperator) :=
  sineSynthesis (reducedFourierMultiplier (responseDerivativeCoefficients i))

theorem multiplierResponse_hasDerivAt_flow (i : Fin 2) (q : PeriodicDomain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => multiplierResponse (HierarchicalLaminates.Periodic.coordinateFlow i q s))
      (multiplierResponseDerivative i (HierarchicalLaminates.Periodic.coordinateFlow i q t)) t := by
  apply hasDerivAt_cosineSynthesis_flow
    (reducedFourierMultiplier rhoSolution)
    (reducedFourierMultiplier (responseDerivativeCoefficients i)) i _ q t
  intro k
  simp only [reducedFourierMultiplier, multiplierCLM_apply,
    responseDerivativeCoefficients_apply, map_smul]

theorem multiplierResponseDerivative_bounded (i : Fin 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q, ‖multiplierResponseDerivative i q‖ ≤ C :=
  ⟨‖multiplierResponseDerivative i‖, norm_nonneg (multiplierResponseDerivative i),
    (multiplierResponseDerivative i).norm_coe_le_norm⟩

def scalarMultiplierResponse (L : ReducedOperator →L[ℝ] ℝ) : C(PeriodicDomain, ℝ) :=
  ⟨fun q => L (multiplierResponse q), L.continuous.comp multiplierResponse.continuous⟩

def scalarMultiplierResponseDerivative (L : ReducedOperator →L[ℝ] ℝ) (i : Fin 2) :
    C(PeriodicDomain, ℝ) :=
  ⟨fun q => L (multiplierResponseDerivative i q),
    L.continuous.comp (multiplierResponseDerivative i).continuous⟩

theorem scalarMultiplierResponse_hasDerivAt_flow
    (L : ReducedOperator →L[ℝ] ℝ) (i : Fin 2) (q : PeriodicDomain) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => scalarMultiplierResponse L (HierarchicalLaminates.Periodic.coordinateFlow i q s))
      (scalarMultiplierResponseDerivative L i (HierarchicalLaminates.Periodic.coordinateFlow i q t)) t :=
  L.hasFDerivAt.comp_hasDerivAt t (multiplierResponse_hasDerivAt_flow i q t)

theorem scalarMultiplierResponseDerivative_bounded
    (L : ReducedOperator →L[ℝ] ℝ) (i : Fin 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q, |scalarMultiplierResponseDerivative L i q| ≤ C := by
  refine ⟨‖scalarMultiplierResponseDerivative L i‖,
    norm_nonneg (scalarMultiplierResponseDerivative L i), ?_⟩
  intro q
  simpa only [Real.norm_eq_abs] using
    (scalarMultiplierResponseDerivative L i).norm_coe_le_norm q

end HierarchicalLaminates.Fourier
