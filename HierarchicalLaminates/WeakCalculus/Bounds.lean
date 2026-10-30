module

public import HierarchicalLaminates.WeakCalculus.Curl
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Elementary L² bounds used by the binary comparison. -/

@[expose] public section
noncomputable section

namespace HierarchicalLaminates.WeakCalculus

open MeasureTheory HierarchicalLaminates.Periodic
open scoped ENNReal

theorem scalarField_norm_le_of_ae_bound (v : ScalarField) {C : ℝ}
    (hC : 0 ≤ C) (hv : ∀ᵐ q ∂domainMeasure, |v q| ≤ C) : ‖v‖ ≤ C := by
  have h := Lp.norm_le_of_ae_bound (f := v) hC
    (by simpa only [Real.norm_eq_abs] using hv)
  simpa [measureUnivNNReal] using h

theorem physicalField_norm_le_sum_components (v : PhysicalField) :
    ‖v‖ ≤ ∑ a : Fin 16, ∑ i : Fin 2, ‖componentField i a v‖ := by
  let s : Fin 16 × Fin 2 → ℝ := fun c => ‖componentField c.2 c.1 v‖
  have hs : ∀ c ∈ Finset.univ, 0 ≤ s c := fun _ _ => norm_nonneg _
  have heq : ‖v‖ ^ 2 = ∑ c : Fin 16 × Fin 2, s c ^ 2 := by
    have h := physical_inner_components v v
    simpa only [real_inner_self_eq_norm_sq, Fintype.sum_prod_type, s] using h
  have hsum := Finset.sum_sq_le_sq_sum_of_nonneg hs
  have hn : 0 ≤ ∑ c : Fin 16 × Fin 2, s c := Finset.sum_nonneg hs
  have hbound : ‖v‖ ≤ ∑ c : Fin 16 × Fin 2, s c := by
    nlinarith [norm_nonneg v]
  simpa only [Fintype.sum_prod_type, s] using hbound

theorem physicalField_norm_le_32_mul (v : PhysicalField) {C : ℝ}
    (hv : ∀ i a, ‖componentField i a v‖ ≤ C) : ‖v‖ ≤ 32 * C := by
  calc
    ‖v‖ ≤ ∑ a : Fin 16, ∑ i : Fin 2, ‖componentField i a v‖ :=
      physicalField_norm_le_sum_components v
    _ ≤ ∑ _a : Fin 16, ∑ _i : Fin 2, C :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun i _ => hv i a))
    _ = 32 * C := by simp; ring

end HierarchicalLaminates.WeakCalculus
