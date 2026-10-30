module

public import HierarchicalLaminates.Fourier.Differentiation
public import HierarchicalLaminates.Fourier.Response
public import HierarchicalLaminates.Lamination.PhysicalSymbol
public import Mathlib.Tactic.FieldSimp

/-!
# Physical potential and gradient multipliers

The multipliers reconstruct the sixteen potential components and their
gradients from the absolutely summable reduced response, using the diagonal
reference law.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Corrector

open Matrix HierarchicalLaminates.Fourier HierarchicalLaminates.Lamination

abbrev PotentialVector := EuclideanSpace ℝ (Fin 16)

lemma verticalDiagonal_bounds (a : Fin 16) :
    (1 / 4 : ℝ) ≤ verticalDiagonalR a ∧ verticalDiagonalR a ≤ 1 := by
  fin_cases a <;> norm_num [verticalDiagonalR]

def denominator (k : HierarchicalLaminates.Frequency) (a : Fin 16) : ℝ :=
  (k.1 : ℝ) ^ 2 + verticalDiagonalR a * (k.2 : ℝ) ^ 2

lemma denominator_nonneg (k : HierarchicalLaminates.Frequency) (a : Fin 16) :
    0 ≤ denominator k a := by
  have hd := (verticalDiagonal_bounds a).1
  dsimp [denominator]
  positivity

lemma denominator_pos {k : HierarchicalLaminates.Frequency} (hx : k.1 ≠ 0) (a : Fin 16) :
    0 < denominator k a := by
  have hx' : (k.1 : ℝ) ≠ 0 := by exact_mod_cast hx
  have hd := (verticalDiagonal_bounds a).1
  exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx')
    (mul_nonneg (by linarith) (sq_nonneg _))

/-- The factor multiplying the sine coefficient before the unit-torus `2π` scaling. -/
def potentialMultiplier (k : HierarchicalLaminates.Frequency) (a : Fin 16) : ℝ :=
  (k.1 : ℝ) / denominator k a

/-- The coordinate derivative multiplier. -/
def gradientMultiplier (k : HierarchicalLaminates.Frequency) (i : Fin 2) (a : Fin 16) : ℝ :=
  (frequencyVector k i : ℝ) * (k.1 : ℝ) / denominator k a

lemma potentialMultiplier_abs_le (k : HierarchicalLaminates.Frequency) (a : Fin 16) :
    |potentialMultiplier k a| ≤ 1 := by
  by_cases hx : k.1 = 0
  · simp [potentialMultiplier, hx]
  · have hd := denominator_pos hx a
    have hxone : (1 : ℝ) ≤ |(k.1 : ℝ)| := by
      exact_mod_cast (Int.one_le_abs hx)
    have hxsq : |(k.1 : ℝ)| ≤ (k.1 : ℝ) ^ 2 := by
      nlinarith [sq_abs (k.1 : ℝ)]
    have hden : (k.1 : ℝ) ^ 2 ≤ denominator k a := by
      have hv := (verticalDiagonal_bounds a).1
      dsimp [denominator]
      nlinarith [sq_nonneg (k.2 : ℝ)]
    rw [potentialMultiplier, abs_div, abs_of_pos hd]
    exact (div_le_one₀ hd).2 (hxsq.trans hden)

lemma gradientMultiplier_abs_le (k : HierarchicalLaminates.Frequency) (i : Fin 2) (a : Fin 16) :
    |gradientMultiplier k i a| ≤ 1 := by
  by_cases hx : k.1 = 0
  · simp [gradientMultiplier, hx]
  · have hd := denominator_pos hx a
    have hv := (verticalDiagonal_bounds a).1
    rw [gradientMultiplier, abs_div, abs_of_pos hd]
    apply (div_le_one₀ hd).2
    fin_cases i
    · simp only [frequencyVector, abs_mul]
      dsimp [denominator]
      nlinarith [sq_nonneg (k.2 : ℝ), sq_abs (k.1 : ℝ)]
    · simp only [frequencyVector, abs_mul]
      dsimp [denominator]
      nlinarith [sq_abs (k.1 : ℝ), sq_abs (k.2 : ℝ),
        sq_nonneg (|(k.1 : ℝ)| - |(k.2 : ℝ)| / 2)]

lemma gradientMultiplier_eq_frequency_mul (k : HierarchicalLaminates.Frequency)
    (i : Fin 2) (a : Fin 16) :
    gradientMultiplier k i a = (frequencyVector k i : ℝ) * potentialMultiplier k a := by
  simp only [gradientMultiplier, potentialMultiplier, mul_div_assoc]

lemma reference_divergence_identity (k : HierarchicalLaminates.Frequency) (a : Fin 16) :
    (k.1 : ℝ) * gradientMultiplier k 0 a +
      verticalDiagonalR a * (k.2 : ℝ) * gradientMultiplier k 1 a = (k.1 : ℝ) := by
  by_cases hx : k.1 = 0
  · simp [gradientMultiplier, hx, frequencyVector]
  · have hd := (denominator_pos hx a).ne'
    simp only [gradientMultiplier, frequencyVector, Matrix.cons_val_zero,
      Matrix.cons_val_succ]
    field_simp
    dsimp [denominator]
    ring

/-- A bounded scalar frequency multiplier, used with its explicit pointwise bound. -/
def scalarMultiplier (m : HierarchicalLaminates.Frequency → ℝ) (C : ℝ)
    (hm : ∀ k, |m k| ≤ C) :
    Coefficients HierarchicalLaminates.Frequency ℝ →L[ℝ] Coefficients HierarchicalLaminates.Frequency ℝ :=
  multiplierCLM (fun k => m k • ContinuousLinearMap.id ℝ ℝ) C (fun k v => by
    simpa only [_root_.smul_apply, ContinuousLinearMap.id_apply,
      norm_smul, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_right (hm k) (abs_nonneg v))

@[simp]
lemma scalarMultiplier_apply (m : HierarchicalLaminates.Frequency → ℝ) (C : ℝ)
    (hm : ∀ k, |m k| ≤ C) (f : Coefficients HierarchicalLaminates.Frequency ℝ) (k) :
    scalarMultiplier m C hm f k = m k * f k := rfl

/-- The physical component of `P X w`, as a bounded operator on reduced matrices. -/
def amplitudeOperator (w : ReducedSpace) (a : Fin 16) : ReducedOperator →L[ℝ] ℝ :=
  (EuclideanSpace.proj (𝕜 := ℝ) a).comp
    ((Matrix.toEuclideanLin factorR).toContinuousLinearMap.comp
      (ContinuousLinearMap.apply ℝ ReducedSpace w))

@[simp]
lemma amplitudeOperator_apply (w : ReducedSpace) (a : Fin 16) (X : ReducedOperator) :
    amplitudeOperator w a X = (factorR *ᵥ (X w : Fin 8 → ℝ)) a := rfl

def amplitudeCoefficients (f : ReducedCoefficients) (w : ReducedSpace) (a : Fin 16) :
    Coefficients HierarchicalLaminates.Frequency ℝ :=
  multiplierCLM (fun _ => amplitudeOperator w a) ‖amplitudeOperator w a‖
    (fun _ X => (amplitudeOperator w a).le_opNorm X) f

@[simp]
lemma amplitudeCoefficients_apply (f : ReducedCoefficients) (w : ReducedSpace)
    (a : Fin 16) (k) :
    amplitudeCoefficients f w a k = amplitudeOperator w a (f k) := rfl

def potentialCoefficients (f : ReducedCoefficients) (w : ReducedSpace) (a : Fin 16) :
    Coefficients HierarchicalLaminates.Frequency ℝ :=
  (2 * Real.pi)⁻¹ • scalarMultiplier (fun k => potentialMultiplier k a) 1
    (fun k => potentialMultiplier_abs_le k a) (amplitudeCoefficients f w a)

def gradientCoefficients (f : ReducedCoefficients) (w : ReducedSpace)
    (i : Fin 2) (a : Fin 16) : Coefficients HierarchicalLaminates.Frequency ℝ :=
  scalarMultiplier (fun k => gradientMultiplier k i a) 1
    (fun k => gradientMultiplier_abs_le k i a) (amplitudeCoefficients f w a)

lemma gradientCoefficients_eq_angular (f : ReducedCoefficients) (w : ReducedSpace)
    (i : Fin 2) (a : Fin 16) (k) :
    gradientCoefficients f w i a k = angularFrequency k i * potentialCoefficients f w a k := by
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  simp only [gradientCoefficients, scalarMultiplier_apply, potentialCoefficients,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, angularFrequency,
    gradientMultiplier_eq_frequency_mul]
  field_simp

/-- A continuous mean-zero real potential on the unit periodic cell. -/
def potential (f : ReducedCoefficients) (w : ReducedSpace) (a : Fin 16) :
    C(PeriodicDomain, ℝ) := sineSynthesis (potentialCoefficients f w a)

def gradientComponent (f : ReducedCoefficients) (w : ReducedSpace)
    (i : Fin 2) (a : Fin 16) : C(PeriodicDomain, ℝ) :=
  cosineSynthesis (gradientCoefficients f w i a)

lemma potential_hasDerivAt (f : ReducedCoefficients) (w : ReducedSpace)
    (i : Fin 2) (a : Fin 16) (q : PeriodicDomain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => potential f w a (HierarchicalLaminates.Periodic.coordinateFlow i q s))
      (gradientComponent f w i a (HierarchicalLaminates.Periodic.coordinateFlow i q t)) t := by
  apply hasDerivAt_sineSynthesis_flow
  intro k
  exact gradientCoefficients_eq_angular f w i a k

lemma potential_mean_zero (f : ReducedCoefficients) (w : ReducedSpace) (a : Fin 16) :
    uniformMean (potential f w a) = 0 := sineSynthesis_mean _

lemma gradientComponent_mean_zero (f : ReducedCoefficients) (w : ReducedSpace)
    (i : Fin 2) (a : Fin 16) : uniformMean (gradientComponent f w i a) = 0 := by
  rw [gradientComponent, cosineSynthesis_mean]
  simp [gradientCoefficients, gradientMultiplier, frequencyVector]

end HierarchicalLaminates.Corrector
