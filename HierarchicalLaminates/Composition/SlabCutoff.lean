module

public import HierarchicalLaminates.Composition.RegularPotential
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Smooth real cutoffs supported inside a horizontal slab. -/

@[expose] public section
noncomputable section

namespace HierarchicalLaminates.Composition

open HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Binary HierarchicalLaminates.Homogenization
open Set Filter
open scoped ContDiff

def rawSlabCutoff (a δ y : ℝ) : ℝ :=
  Real.smoothTransition ((y - δ) / δ) *
    Real.smoothTransition ((a - δ - y) / δ)

theorem rawSlabCutoff_contDiff (a δ : ℝ) :
    ContDiff ℝ ∞ (rawSlabCutoff a δ) := by
  unfold rawSlabCutoff
  fun_prop

theorem rawSlabCutoff_nonneg (a δ y : ℝ) : 0 ≤ rawSlabCutoff a δ y :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem rawSlabCutoff_le_one (a δ y : ℝ) : rawSlabCutoff a δ y ≤ 1 := by
  exact (mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _)
    (Real.smoothTransition.nonneg _)).trans (by simpa using Real.smoothTransition.le_one ((a - δ - y) / δ))

theorem rawSlabCutoff_zero_left (a : ℝ) {δ y : ℝ} (hδ : 0 < δ) (hy : y ≤ δ) :
    rawSlabCutoff a δ y = 0 := by
  rw [rawSlabCutoff, Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hy) hδ.le), zero_mul]

theorem rawSlabCutoff_zero_right {a δ y : ℝ} (hδ : 0 < δ) (hy : a - δ ≤ y) :
    rawSlabCutoff a δ y = 0 := by
  rw [rawSlabCutoff, Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hy) hδ.le), mul_zero]

theorem rawSlabCutoff_one {a δ y : ℝ} (hδ : 0 < δ)
    (hy₀ : 2 * δ ≤ y) (hy₁ : y ≤ a - 2 * δ) :
    rawSlabCutoff a δ y = 1 := by
  rw [rawSlabCutoff, Real.smoothTransition.one_of_one_le
    ((le_div_iff₀ hδ).mpr (by linarith)),
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ hδ).mpr (by linarith)), one_mul]

def rawSlabCutoffDerivative (a δ : ℝ) : ℝ → ℝ := deriv (rawSlabCutoff a δ)

theorem rawSlabCutoff_hasDerivAt (a δ y : ℝ) :
    HasDerivAt (rawSlabCutoff a δ) (rawSlabCutoffDerivative a δ y) y :=
  ((rawSlabCutoff_contDiff a δ).differentiable (by simp)).differentiableAt.hasDerivAt

theorem rawSlabCutoffDerivative_continuous (a δ : ℝ) :
    Continuous (rawSlabCutoffDerivative a δ) :=
  (rawSlabCutoff_contDiff a δ).continuous_deriv (by simp)

theorem rawSlabCutoffDerivative_zero_of_zero {a δ y : ℝ}
    (hy : rawSlabCutoff a δ y = 0) : rawSlabCutoffDerivative a δ y = 0 := by
  have hm : IsLocalMin (rawSlabCutoff a δ) y :=
    Filter.Eventually.of_forall (fun z => by rw [hy]; exact rawSlabCutoff_nonneg a δ z)
  exact hm.hasDerivAt_eq_zero (rawSlabCutoff_hasDerivAt a δ y)

theorem rawSlabCutoffDerivative_zero_of_one {a δ y : ℝ}
    (hy : rawSlabCutoff a δ y = 1) : rawSlabCutoffDerivative a δ y = 0 := by
  have hm : IsLocalMax (rawSlabCutoff a δ) y :=
    Filter.Eventually.of_forall (fun z => by rw [hy]; exact rawSlabCutoff_le_one a δ z)
  exact hm.hasDerivAt_eq_zero (rawSlabCutoff_hasDerivAt a δ y)

theorem rawSlabCutoffDerivative_zero_left (a : ℝ) {δ y : ℝ}
    (hδ : 0 < δ) (hy : y ≤ δ) : rawSlabCutoffDerivative a δ y = 0 :=
  rawSlabCutoffDerivative_zero_of_zero (rawSlabCutoff_zero_left a hδ hy)

theorem rawSlabCutoffDerivative_zero_right {a δ y : ℝ}
    (hδ : 0 < δ) (hy : a - δ ≤ y) : rawSlabCutoffDerivative a δ y = 0 :=
  rawSlabCutoffDerivative_zero_of_zero (rawSlabCutoff_zero_right hδ hy)

end HierarchicalLaminates.Composition
