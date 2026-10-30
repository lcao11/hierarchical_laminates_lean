module

public import HierarchicalLaminates.Composition.LocalizedPotentialInterfaceBound

/-!
# Quantitative L² approximation by localized gradients
-/

@[expose] public section
noncomputable section

namespace HierarchicalLaminates.Composition

open HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.WeakCalculus

theorem aspectErrorField_norm_le (a δ : ℝ) (r k : ℕ) (u : RegularPotential)
    (i : Fin 2) (c : Fin 16) :
    ‖aspectErrorField a δ r k u i c‖ ≤ |(k : ℝ) / (a * r) - 1| * ‖u.gradient‖ :=
  boundedScalarField_norm_le _ _ _ (mul_nonneg (abs_nonneg _) (norm_nonneg _))
    (aspectErrorValue_bound a δ r k u i c)

theorem derivativeErrorField_norm_le (a δ : ℝ) (r k : ℕ) (u : RegularPotential)
    (i : Fin 2) (c : Fin 16) :
    ‖derivativeErrorField a δ r k u i c‖ ≤
      (r : ℝ)⁻¹ * cutoffDerivativeBound a δ * potentialBound u :=
  boundedScalarField_norm_le _ _ _
    (mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg r))
      (cutoffDerivativeBound_nonneg a δ)) (potentialBound_nonneg u))
    (derivativeErrorValue_bound a δ r k u i c)

theorem localizedPotential_error_bound {a δ : ℝ} (ha₀ : 0 < a) (ha : a ≤ 1)
    (hδ : 0 < δ) (hδa : δ < a / 4) {r : ℕ} (hr : 0 < r) (k : ℕ)
    (u : RegularPotential) :
    ‖(localizedPotential ha₀ ha hδ hr k u).field - u.slabField a r k‖ ≤
      32 * (‖u.gradient‖ * Real.sqrt (4 * δ) +
        |(k : ℝ) / (a * r) - 1| * ‖u.gradient‖ +
        (r : ℝ)⁻¹ * cutoffDerivativeBound a δ * potentialBound u) := by
  apply physicalField_norm_le_32_mul
  intro i c
  rw [localizedPotential_component_error ha₀ ha hδ hr k u i c]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add
      (cutoffMismatchField_norm_le ha₀ ha hδ hδa r k u i c)
      (aspectErrorField_norm_le a δ r k u i c)))
    (derivativeErrorField_norm_le a δ r k u i c))

end HierarchicalLaminates.Composition
