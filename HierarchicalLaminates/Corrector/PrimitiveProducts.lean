module

public import HierarchicalLaminates.Corrector.WeakProduct
public import HierarchicalLaminates.Binary.SampledProfileEstimate

/-!
# Bounds for primitive products in the residual
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Corrector

open HierarchicalLaminates.Periodic HierarchicalLaminates.Binary

lemma primitiveProduct_norm_le {N : ℕ} (hN : 0 < N) (s : C(Domain, ℝ)) :
    ‖continuousProduct s (binaryPrimitiveField N hN)‖ ≤ ‖s‖ / (4 * (N : ℝ)) := by
  refine (continuousProduct_norm_le s _).trans ?_
  have h := mul_le_mul_of_nonneg_left (binaryPrimitiveField_norm_le hN) (norm_nonneg s)
  simpa only [mul_one_div] using h

lemma sampledErrorProduct_norm_le {N : ℕ} (hN : 0 < N) (s : C(Domain, ℝ)) :
    ‖continuousProduct s (sampledProfileErrorField N hN)‖ ≤
      ‖s‖ * ‖verticalProfileDerivative‖ / (N : ℝ) := by
  refine (continuousProduct_norm_le s _).trans ?_
  have h := mul_le_mul_of_nonneg_left (sampledProfileErrorField_norm_le hN) (norm_nonneg s)
  simpa only [mul_div_assoc] using h

lemma horizontalDerivativeProduct_norm_le {N : ℕ} (hN : 0 < N) (s : C(Domain, ℝ)) :
    ‖continuousProduct s (binaryHorizontalDerivativeField N hN)‖ ≤
      ‖s‖ * ‖horizontalProfileDerivative‖ / (N : ℝ) := by
  refine (continuousProduct_norm_le s _).trans ?_
  have h := mul_le_mul_of_nonneg_left (binaryHorizontalDerivativeField_norm_le hN) (norm_nonneg s)
  convert h using 1
  ring

end HierarchicalLaminates.Corrector
