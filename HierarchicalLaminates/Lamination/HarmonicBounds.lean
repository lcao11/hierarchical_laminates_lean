module

public import HierarchicalLaminates.Lamination.MatrixOrder
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Ring

/-!
# Order bounds for weighted harmonic means

The proportions range over the whole closed unit interval, including its
endpoints. These are the order estimates used to preserve the compact
material family under every layering step.
-/

@[expose] public section

namespace HierarchicalLaminates.Lamination

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

def matrixAverage (weight : ℝ) (A B : Matrix n n ℝ) : Matrix n n ℝ :=
  weight • A + (1 - weight) • B

omit [Fintype n] [DecidableEq n] in
theorem average_posSemidef {weight : ℝ} (hweight₀ : 0 ≤ weight) (hweight₁ : weight ≤ 1)
    {A B : Matrix n n ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (matrixAverage weight A B).PosSemidef :=
  (hA.smul hweight₀).add (hB.smul (sub_nonneg.mpr hweight₁))

omit [Fintype n] [DecidableEq n] in
theorem average_posDef {weight : ℝ} (hweight₀ : 0 ≤ weight) (hweight₁ : weight ≤ 1)
    {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    (matrixAverage weight A B).PosDef := by
  by_cases hzero : weight = 0
  · simpa [matrixAverage, hzero] using hB
  · exact (hA.smul (lt_of_le_of_ne hweight₀ (Ne.symm hzero))).add_posSemidef
      (hB.posSemidef.smul (sub_nonneg.mpr hweight₁))

omit [Fintype n] [DecidableEq n] in
theorem average_lower_bound {weight : ℝ} (hweight₀ : 0 ≤ weight) (hweight₁ : weight ≤ 1)
    {A B L : Matrix n n ℝ} (hA : (A - L).PosSemidef)
    (hB : (B - L).PosSemidef) : (matrixAverage weight A B - L).PosSemidef := by
  have hid : matrixAverage weight A B - L = matrixAverage weight (A - L) (B - L) := by
    ext i j
    simp only [matrixAverage, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul]
    ring
  rw [hid]
  exact average_posSemidef hweight₀ hweight₁ hA hB

omit [Fintype n] [DecidableEq n] in
theorem average_upper_bound {weight : ℝ} (hweight₀ : 0 ≤ weight) (hweight₁ : weight ≤ 1)
    {A B U : Matrix n n ℝ} (hA : (U - A).PosSemidef)
    (hB : (U - B).PosSemidef) : (U - matrixAverage weight A B).PosSemidef := by
  have hid : U - matrixAverage weight A B = matrixAverage weight (U - A) (U - B) := by
    ext i j
    simp only [matrixAverage, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul]
    ring
  rw [hid]
  exact average_posSemidef hweight₀ hweight₁ hA hB

def harmonicMean (weight : ℝ) (A B : Matrix n n ℝ) : Matrix n n ℝ :=
  (matrixAverage weight A⁻¹ B⁻¹)⁻¹

/-- If both positive matrices lie in a positive order interval, their
weighted harmonic mean lies in the same interval. -/
theorem harmonicMean_bounds {weight : ℝ} (hweight₀ : 0 ≤ weight) (hweight₁ : weight ≤ 1)
    {A B L U : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosDef)
    (hL : L.PosDef) (hU : U.PosDef)
    (hLA : (A - L).PosSemidef) (hLB : (B - L).PosSemidef)
    (hAU : (U - A).PosSemidef) (hBU : (U - B).PosSemidef) :
    (harmonicMean weight A B).PosDef ∧
    (harmonicMean weight A B - L).PosSemidef ∧
    (U - harmonicMean weight A B).PosSemidef := by
  let K := matrixAverage weight A⁻¹ B⁻¹
  have hK : K.PosDef := average_posDef hweight₀ hweight₁ hA.inv hB.inv
  have hKlower : (K - U⁻¹).PosSemidef :=
    average_lower_bound hweight₀ hweight₁
      (inverse_order_reversal hA hU hAU)
      (inverse_order_reversal hB hU hBU)
  have hKupper : (L⁻¹ - K).PosSemidef :=
    average_upper_bound hweight₀ hweight₁
      (inverse_order_reversal hL hA hLA)
      (inverse_order_reversal hL hB hLB)
  have hlower := inverse_order_reversal hK hL.inv hKupper
  have hupper := inverse_order_reversal hU.inv hK hKlower
  let _ := hL.isUnit.invertible
  let _ := hU.isUnit.invertible
  refine ⟨hK.inv, ?_, ?_⟩
  · change (K⁻¹ - L).PosSemidef
    simpa only [Matrix.inv_inv_of_invertible] using hlower
  · change (U - K⁻¹).PosSemidef
    simpa only [Matrix.inv_inv_of_invertible] using hupper

end

end HierarchicalLaminates.Lamination
