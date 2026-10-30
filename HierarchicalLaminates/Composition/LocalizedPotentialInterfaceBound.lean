module

public import HierarchicalLaminates.Composition.LocalizedPotentialBounds
public import HierarchicalLaminates.Composition.InterfaceBounds

/-! The cutoff mismatch is supported on the two shrinking interface bands. -/

@[expose] public section
noncomputable section

namespace HierarchicalLaminates.Composition

open MeasureTheory HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Binary

theorem cutoffMismatchField_norm_le {a δ : ℝ} (ha₀ : 0 < a) (ha : a ≤ 1)
    (hδ : 0 < δ) (hδa : δ < a/4) (r k : ℕ) (u : RegularPotential)
    (i : Fin 2) (c : Fin 16) :
    ‖cutoffMismatchField a δ r k u i c‖ ≤ ‖u.gradient‖ * Real.sqrt (4*δ) := by
  have h := interface_norm_le (a := a) (w := 2*δ) ⟨ha₀,ha⟩
    (by positivity : 0 < 2*δ) (by linarith : 2*δ < a/2) (norm_nonneg u.gradient)
    (cutoffMismatchField a δ r k u i c) ?_ ?_ ?_
  · simpa only [show (2 : ℝ)*(2*δ) = 4*δ by ring] using h
  · filter_upwards [boundedScalarField_coe (cutoffMismatchValue a δ r k u i c)
      (cutoffMismatchValue_measurable a δ r k u i c) ‖u.gradient‖
      (cutoffMismatchValue_bound a δ r k u i c)] with q hq
    change cutoffMismatchField a δ r k u i c q = cutoffMismatchValue a δ r k u i c q at hq
    rw [hq,Real.norm_eq_abs]
    exact cutoffMismatchValue_bound a δ r k u i c q
  · filter_upwards [boundedScalarField_coe (cutoffMismatchValue a δ r k u i c)
      (cutoffMismatchValue_measurable a δ r k u i c) ‖u.gradient‖
      (cutoffMismatchValue_bound a δ r k u i c)] with q hq
    change cutoffMismatchField a δ r k u i c q = cutoffMismatchValue a δ r k u i c q at hq
    intro hy₀ hy₁
    rw [hq,cutoffMismatchValue,rawSlabCutoff_one hδ hy₀ hy₁.le,sub_self,zero_mul]
  · filter_upwards [boundedScalarField_coe (cutoffMismatchValue a δ r k u i c)
      (cutoffMismatchValue_measurable a δ r k u i c) ‖u.gradient‖
      (cutoffMismatchValue_bound a δ r k u i c)] with q hq
    change cutoffMismatchField a δ r k u i c q = cutoffMismatchValue a δ r k u i c q at hq
    intro hy
    rw [hq,cutoffMismatchValue,slabValue,ite_eq_right (not_lt.mpr hy),mul_zero]

end HierarchicalLaminates.Composition
