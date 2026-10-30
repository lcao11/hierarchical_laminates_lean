module

public import HierarchicalLaminates.Fourier.KernelDerivatives
public import HierarchicalLaminates.Fourier.CosineProfile
public import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Differentiating uniformly convergent Fourier synthesis

Summability of the frequency-weighted coefficients gives the derivative of
the infinite periodic field by termwise differentiation.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Fourier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def angularFrequency (k : ℤ × ℤ) (i : Fin 2) : ℝ :=
  2 * Real.pi * (frequencyVector k i : ℝ)

theorem hasDerivAt_sineSynthesis_flow
    (f g : Coefficients (ℤ × ℤ) E) (i : Fin 2)
    (hg : ∀ k, g k = angularFrequency k i • f k)
    (q : PeriodicDomain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => sineSynthesis f (HierarchicalLaminates.Periodic.coordinateFlow i q s))
      (cosineSynthesis g (HierarchicalLaminates.Periodic.coordinateFlow i q t)) t := by
  have hterm (k : ℤ × ℤ) (s : ℝ) :
      HasDerivAt
        (fun y : ℝ => sineKernel k (HierarchicalLaminates.Periodic.coordinateFlow i q y) • f k)
        (cosineKernel k (HierarchicalLaminates.Periodic.coordinateFlow i q s) • g k) s := by
    convert (hasDerivAt_sineKernel_flow_at k i q s).smul_const (f k) using 1
    rw [hg k]
    simp only [angularFrequency, smul_smul]
    congr 1
    ring
  have hbound (k : ℤ × ℤ) (s : ℝ) :
      ‖cosineKernel k (HierarchicalLaminates.Periodic.coordinateFlow i q s) • g k‖ ≤ ‖g k‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (cosineKernel_abs_le _ _)
  have hbase : Summable (fun k : ℤ × ℤ =>
      sineKernel k (HierarchicalLaminates.Periodic.coordinateFlow i q (0 : ℝ)) • f k) :=
    pointwiseSynthesis_summable sineKernel sineKernel_norm_le f _
  have h := hasDerivAt_tsum (coefficients_summable_norm g) hterm hbound hbase t
  simpa only [sineSynthesis, cosineSynthesis,
    continuousSynthesis_apply sineKernel sineKernel_norm_le,
    continuousSynthesis_apply cosineKernel cosineKernel_norm_le] using h

theorem hasDerivAt_cosineSynthesis_flow
    (f g : Coefficients (ℤ × ℤ) E) (i : Fin 2)
    (hg : ∀ k, g k = -(angularFrequency k i) • f k)
    (q : PeriodicDomain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => cosineSynthesis f (HierarchicalLaminates.Periodic.coordinateFlow i q s))
      (sineSynthesis g (HierarchicalLaminates.Periodic.coordinateFlow i q t)) t := by
  have hterm (k : ℤ × ℤ) (s : ℝ) :
      HasDerivAt
        (fun y : ℝ => cosineKernel k (HierarchicalLaminates.Periodic.coordinateFlow i q y) • f k)
        (sineKernel k (HierarchicalLaminates.Periodic.coordinateFlow i q s) • g k) s := by
    convert (hasDerivAt_cosineKernel_flow_at k i q s).smul_const (f k) using 1
    rw [hg k]
    simp only [angularFrequency, smul_smul]
    congr 1
    ring
  have hbound (k : ℤ × ℤ) (s : ℝ) :
      ‖sineKernel k (HierarchicalLaminates.Periodic.coordinateFlow i q s) • g k‖ ≤ ‖g k‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (sineKernel_abs_le _ _)
  have hbase : Summable (fun k : ℤ × ℤ =>
      cosineKernel k (HierarchicalLaminates.Periodic.coordinateFlow i q (0 : ℝ)) • f k) :=
    pointwiseSynthesis_summable cosineKernel cosineKernel_norm_le f _
  have h := hasDerivAt_tsum (coefficients_summable_norm g) hterm hbound hbase t
  simpa only [sineSynthesis, cosineSynthesis,
    continuousSynthesis_apply sineKernel sineKernel_norm_le,
    continuousSynthesis_apply cosineKernel cosineKernel_norm_le] using h

end HierarchicalLaminates.Fourier
