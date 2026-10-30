module

public import HierarchicalLaminates.Corrector.BinaryFlux
public import HierarchicalLaminates.Corrector.ConstitutiveDifference
public import HierarchicalLaminates.Corrector.PrimitiveProducts
public import HierarchicalLaminates.WeakCalculus.Bounds

/-!
# The binary constitutive residual tends to zero

The residual compares the binary coefficient field with the smooth corrector.
Its estimate includes the error from sampling the phase-fraction profile.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Corrector

open HierarchicalLaminates.Periodic HierarchicalLaminates.Material HierarchicalLaminates.Binary HierarchicalLaminates.WeakCalculus

lemma binaryResidual_rearrange (N : ℕ) (hN : 0 < N) (z : PotentialVector) :
    binaryResidual N hN z =
      (coefficientLaw smoothFraction (continuousField (totalContinuous z)) -
        coefficientLaw (binaryFraction N) (continuousField (totalContinuous z))) +
      HierarchicalLaminates.rho • curlField
        (productGradient (binaryPrimitiveField N hN) (binaryPrimitiveDerivativeFields N hN) z) := by
  unfold binaryResidual comparisonResidual binaryTrialFlux correctedFlux
  abel

lemma binaryResidual_component_zero (N : ℕ) (hN : 0 < N) (z : PotentialVector) (a : Fin 16) :
    componentField 0 a (binaryResidual N hN z) =
      HierarchicalLaminates.rho • (continuousProduct (sourceComponent z a) (sampledProfileErrorField N hN) -
        continuousProduct (sourceDerivative z a 1) (binaryPrimitiveField N hN)) := by
  rw [binaryResidual_rearrange, map_add, map_smul, curlField_component_zero,
    binary_constitutive_difference_zero N hN z a, productGradient, component_assembleField]
  simp only [productGradientComponents, binaryPrimitiveDerivativeFields, Matrix.cons_val_one,
    Matrix.cons_val_zero, continuousProduct_add_right]
  module

lemma binaryResidual_component_one (N : ℕ) (hN : 0 < N) (z : PotentialVector) (a : Fin 16) :
    componentField 1 a (binaryResidual N hN z) =
      HierarchicalLaminates.rho • (continuousProduct (sourceComponent z a) (binaryHorizontalDerivativeField N hN) +
        continuousProduct (sourceDerivative z a 0) (binaryPrimitiveField N hN)) := by
  rw [binaryResidual_rearrange, map_add, map_smul, curlField_component_one,
    binary_constitutive_difference_one N hN z a, zero_add, productGradient, component_assembleField]
  rfl

lemma binaryResidual_component_zero_norm (N : ℕ) (hN : 0 < N) (z : PotentialVector) (a : Fin 16) :
    ‖componentField 0 a (binaryResidual N hN z)‖ ≤
      HierarchicalLaminates.rho * (‖sourceComponent z a‖ * ‖verticalProfileDerivative‖ +
        ‖sourceDerivative z a 1‖ / 4) / (N : ℝ) := by
  rw [binaryResidual_component_zero, norm_smul, Real.norm_eq_abs,
    abs_of_pos HierarchicalLaminates.rho_pos]
  refine (mul_le_mul_of_nonneg_left (norm_sub_le _ _) HierarchicalLaminates.rho_pos.le).trans ?_
  have he := sampledErrorProduct_norm_le hN (sourceComponent z a)
  have hp := primitiveProduct_norm_le hN (sourceDerivative z a 1)
  have h := mul_le_mul_of_nonneg_left (add_le_add he hp) HierarchicalLaminates.rho_pos.le
  convert h using 1
  ring

lemma binaryResidual_component_one_norm (N : ℕ) (hN : 0 < N) (z : PotentialVector) (a : Fin 16) :
    ‖componentField 1 a (binaryResidual N hN z)‖ ≤
      HierarchicalLaminates.rho * (‖sourceComponent z a‖ * ‖horizontalProfileDerivative‖ +
        ‖sourceDerivative z a 0‖ / 4) / (N : ℝ) := by
  rw [binaryResidual_component_one, norm_smul, Real.norm_eq_abs,
    abs_of_pos HierarchicalLaminates.rho_pos]
  refine (mul_le_mul_of_nonneg_left (norm_add_le _ _) HierarchicalLaminates.rho_pos.le).trans ?_
  have he := horizontalDerivativeProduct_norm_le hN (sourceComponent z a)
  have hp := primitiveProduct_norm_le hN (sourceDerivative z a 0)
  have h := mul_le_mul_of_nonneg_left (add_le_add he hp) HierarchicalLaminates.rho_pos.le
  convert h using 1
  ring

def binaryResidualRate (z : PotentialVector) : ℝ :=
  ∑ a : Fin 16, HierarchicalLaminates.rho *
    (‖sourceComponent z a‖ * (‖verticalProfileDerivative‖ + ‖horizontalProfileDerivative‖) +
      (‖sourceDerivative z a 0‖ + ‖sourceDerivative z a 1‖) / 4)

lemma binaryResidualRate_nonneg (z : PotentialVector) : 0 ≤ binaryResidualRate z := by
  apply Finset.sum_nonneg
  intro a _
  exact mul_nonneg HierarchicalLaminates.rho_pos.le (by positivity)

lemma binaryResidual_norm_le (N : ℕ) (hN : 0 < N) (z : PotentialVector) :
    ‖binaryResidual N hN z‖ ≤ binaryResidualRate z / (N : ℝ) := by
  calc
    ‖binaryResidual N hN z‖ ≤ ∑ a : Fin 16, ∑ i : Fin 2,
        ‖componentField i a (binaryResidual N hN z)‖ :=
      physicalField_norm_le_sum_components _
    _ ≤ ∑ a : Fin 16,
        (HierarchicalLaminates.rho * (‖sourceComponent z a‖ * ‖verticalProfileDerivative‖ +
          ‖sourceDerivative z a 1‖ / 4) / (N : ℝ) +
        HierarchicalLaminates.rho * (‖sourceComponent z a‖ * ‖horizontalProfileDerivative‖ +
          ‖sourceDerivative z a 0‖ / 4) / (N : ℝ)) := by
      apply Finset.sum_le_sum
      intro a _
      rw [Fin.sum_univ_two]
      exact add_le_add (binaryResidual_component_zero_norm N hN z a)
        (binaryResidual_component_one_norm N hN z a)
    _ = binaryResidualRate z / (N : ℝ) := by
      rw [binaryResidualRate, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      ring

end HierarchicalLaminates.Corrector
