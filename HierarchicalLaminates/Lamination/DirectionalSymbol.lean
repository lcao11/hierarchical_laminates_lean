module

public import HierarchicalLaminates.Algebra.Positivity
public import HierarchicalLaminates.Lamination.HarmonicBounds
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Positivity

/-!
# The reduced multiplier in arbitrary real directions

The formula applies to every real lamination normal and specializes to
integer Fourier frequencies.
-/

@[expose] public section

namespace HierarchicalLaminates.Lamination

open Matrix

noncomputable section

def directionalDegreeR (j : Fin 4) : ℝ := (j.val : ℝ) + 1

def directionalWeightR (k : ℝ × ℝ) (j : Fin 4) : ℝ :=
  directionalDegreeR j * k.1 ^ 2 /
    (4 * (directionalDegreeR j * k.1 ^ 2 + k.2 ^ 2))

def directionalSymbolR (k : ℝ × ℝ) : RMatrix8 :=
  ∑ j : Fin 4, directionalWeightR k j • ((1 : RMatrix8) + gammaR j)

theorem directionalDegreeR_pos (j : Fin 4) : 0 < directionalDegreeR j := by
  dsimp [directionalDegreeR]
  positivity

theorem directionalWeightR_nonneg (k : ℝ × ℝ) (j : Fin 4) :
    0 ≤ directionalWeightR k j := by
  unfold directionalWeightR
  exact div_nonneg (mul_nonneg (directionalDegreeR_pos j).le (sq_nonneg _))
    (mul_nonneg (by norm_num)
      (add_nonneg (mul_nonneg (directionalDegreeR_pos j).le (sq_nonneg _))
        (sq_nonneg _)))

theorem directionalWeightR_le_quarter (k : ℝ × ℝ) (j : Fin 4) :
    directionalWeightR k j ≤ 1 / 4 := by
  have hnum : 0 ≤ directionalDegreeR j * k.1 ^ 2 :=
    mul_nonneg (directionalDegreeR_pos j).le (sq_nonneg _)
  by_cases hzero : directionalDegreeR j * k.1 ^ 2 + k.2 ^ 2 = 0
  · simp [directionalWeightR, hzero]
  · have hden : 0 < directionalDegreeR j * k.1 ^ 2 + k.2 ^ 2 :=
      lt_of_le_of_ne (add_nonneg hnum (sq_nonneg _)) (Ne.symm hzero)
    unfold directionalWeightR
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hden)).2
    nlinarith [sq_nonneg k.2]

theorem directionalWeightR_pos {k : ℝ × ℝ} (hk : k.1 ≠ 0) (j : Fin 4) :
    0 < directionalWeightR k j := by
  have hnum := mul_pos (directionalDegreeR_pos j) (sq_pos_of_ne_zero hk)
  exact div_pos hnum
    (mul_pos (by norm_num) (add_pos_of_pos_of_nonneg hnum (sq_nonneg _)))

theorem directionalSymbolR_mem (k : ℝ × ℝ) : directionalSymbolR k ∈ parameterSpace := by
  apply parameterSpace.sum_mem
  intro j _
  exact parameterSpace.smul_mem (directionalWeightR k j)
    (parameterSpace.add_mem parameterSpace_one_mem (parameterSpace_gamma_mem j))

theorem directionalSymbolR_posSemidef (k : ℝ × ℝ) : (directionalSymbolR k).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro j _
  exact (gammaR_add_identity_posSemidef j).smul (directionalWeightR_nonneg k j)

theorem gramR_eq_piece_sum :
    gramR = ∑ j : Fin 4, (1 / 4 : ℝ) • ((1 : RMatrix8) + gammaR j) := by
  rw [gramR_eq, gammaSumR_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  module

theorem directionalSymbolR_upper_gram (k : ℝ × ℝ) :
    (gramR - directionalSymbolR k).PosSemidef := by
  have hid : gramR - directionalSymbolR k =
      ∑ j : Fin 4, (1 / 4 - directionalWeightR k j) •
        ((1 : RMatrix8) + gammaR j) := by
    rw [gramR_eq_piece_sum, directionalSymbolR]
    simp only [sub_smul, Finset.sum_sub_distrib]
  rw [hid]
  apply Matrix.posSemidef_sum
  intro j _
  exact (gammaR_add_identity_posSemidef j).smul
    (sub_nonneg.mpr (directionalWeightR_le_quarter k j))

theorem directionalSymbolR_upper_three_halves (k : ℝ × ℝ) :
    ((3 / 2 : ℝ) • (1 : RMatrix8) - directionalSymbolR k).PosSemidef := by
  have h := gramR_upper_posSemidef.add (directionalSymbolR_upper_gram k)
  convert h using 1; abel

theorem directionalSymbolR_posDef {k : ℝ × ℝ} (hk : k.1 ≠ 0) :
    (directionalSymbolR k).PosDef := by
  let δ := min (min (directionalWeightR k 0) (directionalWeightR k 1))
    (min (directionalWeightR k 2) (directionalWeightR k 3))
  have hδpos : 0 < δ :=
    lt_min (lt_min (directionalWeightR_pos hk 0) (directionalWeightR_pos hk 1))
      (lt_min (directionalWeightR_pos hk 2) (directionalWeightR_pos hk 3))
  have hδle (j : Fin 4) : δ ≤ directionalWeightR k j := by
    fin_cases j
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact (min_le_left _ _).trans (min_le_right _ _)
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have hsplit : directionalSymbolR k = (4 * δ) • gramR +
      ∑ j : Fin 4, (directionalWeightR k j - δ) •
        ((1 : RMatrix8) + gammaR j) := by
    rw [directionalSymbolR, gramR_eq_piece_sum]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    module
  have hbase : ((4 * δ) • gramR).PosDef :=
    gramR_posDef.smul (mul_pos (by norm_num) hδpos)
  have hrest : (∑ j : Fin 4, (directionalWeightR k j - δ) •
      ((1 : RMatrix8) + gammaR j)).PosSemidef := by
    apply Matrix.posSemidef_sum
    intro j _
    exact (gammaR_add_identity_posSemidef j).smul (sub_nonneg.mpr (hδle j))
  rw [hsplit]
  exact hbase.add_posSemidef hrest

@[simp]
theorem directionalSymbolR_vertical (ky : ℝ) : directionalSymbolR (0, ky) = 0 := by
  simp [directionalSymbolR, directionalWeightR]

def directionalLambdaR (k : ℝ × ℝ) : RMatrix8 := (directionalSymbolR k)⁻¹

theorem directionalLambdaR_mem {k : ℝ × ℝ} (hk : k.1 ≠ 0) :
    directionalLambdaR k ∈ parameterSpace :=
  parameterSpace_inv_mem (directionalSymbolR_mem k) (directionalSymbolR_posDef hk)

theorem directionalLambdaR_posDef {k : ℝ × ℝ} (hk : k.1 ≠ 0) :
    (directionalLambdaR k).PosDef := (directionalSymbolR_posDef hk).inv

theorem directionalLambdaR_lower {k : ℝ × ℝ} (hk : k.1 ≠ 0) :
    (directionalLambdaR k - (2 / 3 : ℝ) • (1 : RMatrix8)).PosSemidef := by
  have hscale : ((3 / 2 : ℝ) • (1 : RMatrix8)).PosDef :=
    Matrix.PosDef.one.smul (by norm_num)
  have hid : ((3 / 2 : ℝ) • (1 : RMatrix8))⁻¹ = (2 / 3 : ℝ) • (1 : RMatrix8) := by
    apply Matrix.inv_eq_right_inv
    norm_num [smul_mul_assoc, mul_smul_comm, smul_smul]
  have h := inverse_order_reversal (directionalSymbolR_posDef hk) hscale
    (directionalSymbolR_upper_three_halves k)
  simpa only [directionalLambdaR, hid] using h

theorem directionalLambdaR_sub_contrast_posDef {k : ℝ × ℝ} (hk : k.1 ≠ 0)
    {ρ : ℝ} (hρ : ρ < 2 / 3) :
    (directionalLambdaR k - ρ • (1 : RMatrix8)).PosDef := by
  have hbase : (((2 / 3 : ℝ) - ρ) • (1 : RMatrix8)).PosDef :=
    Matrix.PosDef.one.smul (sub_pos.mpr hρ)
  have h := hbase.add_posSemidef (directionalLambdaR_lower hk)
  convert h using 1
  module

end

end HierarchicalLaminates.Lamination
