module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Tactic.NormNum

/-!
# Operators on absolutely summable Fourier sequences

Reindexing, frequency shifts and bounded multipliers act on ℓ¹ sequences
with values in a real normed space. Scalar linearity is over `ℝ`, including
when the coefficient space also carries a complex structure.
-/

@[expose] public section

noncomputable section

open scoped lp ENNReal

namespace HierarchicalLaminates.Fourier

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

abbrev Coefficients (ι E : Type*) [NormedAddCommGroup E] := ℓ¹(ι, E)

theorem coefficients_norm_eq (f : Coefficients ι E) :
    ‖f‖ = ∑' i, ‖f i‖ := by
  simpa using lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal) f

theorem coefficients_summable_norm (f : Coefficients ι E) :
    Summable (fun i => ‖f i‖) := by
  simpa using (lp.memℓp f).summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)

/-- Reindex an absolutely summable coefficient sequence by a bijection. -/
def reindexSequence (e : ι ≃ ι) (f : Coefficients ι E) : Coefficients ι E :=
  ⟨fun i => f (e i), by
    apply memℓp_gen
    simpa only [Function.comp_def, ENNReal.toReal_one, Real.rpow_one] using
      e.summable_iff.mpr (coefficients_summable_norm f)⟩

@[simp]
theorem reindexSequence_apply (e : ι ≃ ι) (f : Coefficients ι E) (i : ι) :
    reindexSequence e f i = f (e i) := rfl

@[simp]
theorem reindexSequence_norm (e : ι ≃ ι) (f : Coefficients ι E) :
    ‖reindexSequence e f‖ = ‖f‖ := by
  rw [coefficients_norm_eq, coefficients_norm_eq]
  exact e.tsum_eq (fun i => ‖f i‖)

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

def reindexLinear (e : ι ≃ ι) : Coefficients ι E →ₗ[ℝ] Coefficients ι E where
  toFun := reindexSequence e
  map_add' f g := by ext i; rfl
  map_smul' c f := by ext i; rfl

/-- Reindexing, regarded as a bounded linear map of norm at most one. -/
def reindexCLM (e : ι ≃ ι) : Coefficients ι E →L[ℝ] Coefficients ι E :=
  (reindexLinear e).mkContinuous 1 (fun f => by simp [reindexLinear])

@[simp]
theorem reindexCLM_apply (e : ι ≃ ι) (f : Coefficients ι E) (i : ι) :
    reindexCLM e f i = f (e i) := rfl

@[simp]
theorem reindexCLM_norm_apply (e : ι ≃ ι) (f : Coefficients ι E) :
    ‖reindexCLM e f‖ = ‖f‖ := reindexSequence_norm e f

section Shifts

variable [AddCommGroup ι]

def subtractEquiv (v : ι) : ι ≃ ι where
  toFun i := i - v
  invFun i := i + v
  left_inv i := by simp
  right_inv i := by simp

/-- A frequency shift acts by `f(k-v)`, the convention for multiplication by a character. -/
def shift (v : ι) : Coefficients ι E →L[ℝ] Coefficients ι E :=
  reindexCLM (subtractEquiv v)

@[simp]
theorem shift_apply (v : ι) (f : Coefficients ι E) (i : ι) :
    shift v f i = f (i - v) := rfl

@[simp]
theorem shift_norm (v : ι) (f : Coefficients ι E) : ‖shift v f‖ = ‖f‖ :=
  reindexCLM_norm_apply _ _

/-- A finite Fourier profile acts by a finite sum of weighted shifts. -/
def weightedShifts {n : ℕ} (v : Fin n → ι) (w : Fin n → ℝ) :
    Coefficients ι E →L[ℝ] Coefficients ι E :=
  ∑ j : Fin n, w j • shift (v j)

theorem weightedShifts_norm_le {n : ℕ} (v : Fin n → ι) (w : Fin n → ℝ)
    (f : Coefficients ι E) :
    ‖weightedShifts v w f‖ ≤ (∑ j : Fin n, |w j|) * ‖f‖ := by
  simp only [weightedShifts, sum_apply, smul_apply]
  calc
    ‖∑ j : Fin n, w j • shift (v j) f‖ ≤
        ∑ j : Fin n, ‖w j • shift (v j) f‖ := norm_sum_le _ _
    _ = (∑ j : Fin n, |w j|) * ‖f‖ := by
      simp only [norm_smul, Real.norm_eq_abs, shift_norm, Finset.sum_mul]

theorem weightedShifts_norm_le_one {n : ℕ} (v : Fin n → ι) (w : Fin n → ℝ)
    (hw : (∑ j : Fin n, |w j|) ≤ 1) (f : Coefficients ι E) :
    ‖weightedShifts v w f‖ ≤ ‖f‖ := by
  exact (weightedShifts_norm_le v w f).trans
    (by simpa using mul_le_mul_of_nonneg_right hw (norm_nonneg f))

end Shifts

section Multipliers

variable (T : ι → E →L[ℝ] F) (C : ℝ) (hT : ∀ i v, ‖T i v‖ ≤ C * ‖v‖)

/-- A uniformly bounded family gives a diagonal map of absolutely summable sequences. -/
def multiplierSequence (f : Coefficients ι E) : Coefficients ι F :=
  ⟨fun i => T i (f i), by
    apply memℓp_gen
    have hs := (coefficients_summable_norm f).mul_left C
    have hn : Summable (fun i => ‖T i (f i)‖) :=
      hs.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hT i (f i))
    simpa using hn⟩

@[simp]
theorem multiplierSequence_apply (f : Coefficients ι E) (i : ι) :
    multiplierSequence T C hT f i = T i (f i) := rfl

theorem multiplierSequence_norm_le (f : Coefficients ι E) :
    ‖multiplierSequence T C hT f‖ ≤ C * ‖f‖ := by
  rw [coefficients_norm_eq, coefficients_norm_eq]
  have hs := (coefficients_summable_norm f).mul_left C
  calc
    (∑' i, ‖multiplierSequence T C hT f i‖) ≤ ∑' i, C * ‖f i‖ :=
      (coefficients_summable_norm _).tsum_le_tsum (fun i => hT i (f i)) hs
    _ = C * ∑' i, ‖f i‖ := tsum_mul_left

def multiplierLinear : Coefficients ι E →ₗ[ℝ] Coefficients ι F where
  toFun := multiplierSequence T C hT
  map_add' f g := by ext i; simp
  map_smul' c f := by ext i; simp

def multiplierCLM : Coefficients ι E →L[ℝ] Coefficients ι F :=
  (multiplierLinear T C hT).mkContinuous C (multiplierSequence_norm_le T C hT)

@[simp]
theorem multiplierCLM_apply (f : Coefficients ι E) (i : ι) :
    multiplierCLM T C hT f i = T i (f i) := rfl

theorem multiplierCLM_norm_le (f : Coefficients ι E) :
    ‖multiplierCLM T C hT f‖ ≤ C * ‖f‖ := multiplierSequence_norm_le T C hT f

end Multipliers

end HierarchicalLaminates.Fourier
