module

public import HierarchicalLaminates.Corrector.Multipliers

/-!
# The physical horizontal gradient and its reduced symbol
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Corrector

open Matrix HierarchicalLaminates.Fourier HierarchicalLaminates.Lamination

lemma horizontal_gradient_matrix (k : HierarchicalLaminates.Frequency) :
    Matrix.diagonal (fun a => gradientMultiplier k 0 a) =
      (k.1 : ℝ) ^ 2 • referenceDirectionInverse (realFrequency k) := by
  ext a b
  by_cases hab : a = b
  · subst b
    simp only [diagonal_apply_eq, Matrix.smul_apply, referenceDirectionInverse]
    simp only [smul_eq_mul, gradientMultiplier,
      frequencyVector, Matrix.cons_val_zero, referenceDirectionDiagonal,
      realFrequency, denominator]
    ring
  · simp [referenceDirectionInverse, hab]

lemma physical_gradient_reduced_symbol (k : HierarchicalLaminates.Frequency) :
    factorRᵀ * Matrix.diagonal (fun a => gradientMultiplier k 0 a) * factorR =
      directionalSymbolR (realFrequency k) := by
  by_cases hx : k.1 = 0
  · simp [gradientMultiplier, hx, realFrequency]
  · have hx' : (realFrequency k).1 ≠ 0 := by
      dsimp [realFrequency]
      exact_mod_cast hx
    rw [horizontal_gradient_matrix, Matrix.mul_smul, Matrix.smul_mul,
      ← referenceDirectionMatrix_inverse hx']
    simpa only [physicalReducedSymbol, realFrequency] using
      physicalReducedSymbol_eq_directionalSymbolR (realFrequency k)

lemma reduced_gradient_coefficients (f : ReducedCoefficients) (w : ReducedSpace)
    (k : HierarchicalLaminates.Frequency) :
    factorRᵀ *ᵥ (fun a => gradientCoefficients f w 0 a k) =
      ((reducedFourierMultiplier f k) w : Fin 8 → ℝ) := by
  have hg : (fun a => gradientCoefficients f w 0 a k) =
      Matrix.diagonal (fun a => gradientMultiplier k 0 a) *ᵥ
        (factorR *ᵥ (f k w : Fin 8 → ℝ)) := by
    ext a
    simp only [gradientCoefficients, scalarMultiplier_apply, amplitudeCoefficients_apply,
      amplitudeOperator_apply, Matrix.mulVec_diagonal]
  rw [hg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, physical_gradient_reduced_symbol]
  rfl

end HierarchicalLaminates.Corrector
