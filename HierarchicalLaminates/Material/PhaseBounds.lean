module

public import HierarchicalLaminates.Lamination.ConstitutiveFamily
public import HierarchicalLaminates.Algebra.Parameters
public import HierarchicalLaminates.Fourier.OperatorNorm
public import Mathlib.Tactic.FinCases

/-!
# Quarter-ellipticity and upper bounds for the two phases
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Material

open HierarchicalLaminates.Lamination Matrix

abbrev PhysicalTensor := Tensor (Fin 16)

theorem spatialBlocks_posSemidef {A D : Matrix (Fin 16) (Fin 16) ℝ}
    (hA : A.PosSemidef) (hD : D.PosSemidef) :
    (spatialBlocks A D).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    rintro ⟨i, a⟩ ⟨j, b⟩
    fin_cases i <;> fin_cases j
    · simpa [spatialBlocks] using hA.isHermitian.apply a b
    · simp [spatialBlocks]
    · simp [spatialBlocks]
    · simpa [spatialBlocks] using hD.isHermitian.apply a b
  · intro v
    change 0 ≤ quadraticEnergy (spatialBlocks A D) v
    rw [spatialBlocks_energy]
    exact add_nonneg
      (by simpa only [quadraticFormValue, star_trivial] using
        hA.dotProduct_mulVec_nonneg (fun a => v (0, a)))
      (by simpa only [quadraticFormValue, star_trivial] using
        hD.dotProduct_mulVec_nonneg (fun a => v (1, a)))

theorem spatialBlocks_sub_identity (A D : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ) :
    spatialBlocks A D - c • (1 : PhysicalTensor) =
      spatialBlocks (A - c • 1) (D - c • 1) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases j <;>
    simp [spatialBlocks, Matrix.one_apply, Matrix.sub_apply]

theorem identity_sub_spatialBlocks (A D : Matrix (Fin 16) (Fin 16) ℝ) :
    (1 : PhysicalTensor) - spatialBlocks A D = spatialBlocks (1 - A) (1 - D) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases j <;>
    simp [spatialBlocks, Matrix.one_apply, Matrix.sub_apply]

theorem phaseZero_lower :
    (phaseZero - (1 / 4 : ℝ) • (1 : PhysicalTensor)).PosSemidef := by
  rw [phaseZero, materialTensor_eq_spatialBlocks, spatialBlocks_sub_identity]
  apply spatialBlocks_posSemidef
  · have heq : horizontalR 0 - (1 / 4 : ℝ) • (1 : Matrix (Fin 16) (Fin 16) ℝ) =
        (3 / 4 : ℝ) • (1 : Matrix (Fin 16) (Fin 16) ℝ) := by
      simp only [horizontalR, Matrix.mul_zero, Matrix.zero_mul, sub_zero]
      module
    rw [heq]
    exact Matrix.PosSemidef.one.smul (by norm_num)
  · exact verticalR_lower_posSemidef

theorem phaseOne_horizontal_lower :
    (horizontalR (rho • (1 : RMatrix8)) -
      (1 / 4 : ℝ) • (1 : Matrix (Fin 16) (Fin 16) ℝ)).PosSemidef := by
  have hcoef : 0 ≤ 3 / 4 - (3 / 2 : ℝ) * rho := by linarith [rho_lt_one_third]
  have hI := Matrix.PosSemidef.one.smul
    (R := ℝ) (n := Fin 16) hcoef
  have hGram := factorR_upper_posSemidef.smul (le_of_lt rho_pos)
  have heq : horizontalR (rho • (1 : RMatrix8)) -
      (1 / 4 : ℝ) • (1 : Matrix (Fin 16) (Fin 16) ℝ) =
      (3 / 4 - (3 / 2 : ℝ) * rho) • (1 : Matrix (Fin 16) (Fin 16) ℝ) +
        rho • ((3 / 2 : ℝ) • (1 : Matrix (Fin 16) (Fin 16) ℝ) -
          factorR * factorRᵀ) := by
    simp only [horizontalR, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      smul_sub, smul_smul]
    module
  rw [heq]
  exact hI.add hGram

theorem phaseOne_lower :
    (phaseOne rho - (1 / 4 : ℝ) • (1 : PhysicalTensor)).PosSemidef := by
  rw [phaseOne, materialTensor_eq_spatialBlocks, spatialBlocks_sub_identity]
  exact spatialBlocks_posSemidef phaseOne_horizontal_lower verticalR_lower_posSemidef

theorem phaseZero_upper : ((1 : PhysicalTensor) - phaseZero).PosSemidef := by
  rw [phaseZero, materialTensor_eq_spatialBlocks, identity_sub_spatialBlocks]
  apply spatialBlocks_posSemidef
  · simpa [horizontalR] using
      (Matrix.PosSemidef.zero : (0 : Matrix (Fin 16) (Fin 16) ℝ).PosSemidef)
  · exact verticalR_upper_posSemidef

theorem phaseOne_upper : ((1 : PhysicalTensor) - phaseOne rho).PosSemidef := by
  rw [phaseOne, materialTensor_eq_spatialBlocks, identity_sub_spatialBlocks]
  exact spatialBlocks_posSemidef
    (horizontalR_upper_posSemidef (Matrix.PosSemidef.one.smul (le_of_lt rho_pos)))
    verticalR_upper_posSemidef

def mixtureTensor (t : ℝ) : PhysicalTensor :=
  (1 - t) • phaseZero + t • phaseOne rho

theorem mixture_lower {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (mixtureTensor t - (1 / 4 : ℝ) • (1 : PhysicalTensor)).PosSemidef := by
  have heq : mixtureTensor t - (1 / 4 : ℝ) • (1 : PhysicalTensor) =
      (1 - t) • (phaseZero - (1 / 4 : ℝ) • 1) +
        t • (phaseOne rho - (1 / 4 : ℝ) • 1) := by
    unfold mixtureTensor
    module
  rw [heq]
  exact (phaseZero_lower.smul (sub_nonneg.mpr ht.2)).add (phaseOne_lower.smul ht.1)

theorem mixture_upper {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ((1 : PhysicalTensor) - mixtureTensor t).PosSemidef := by
  have heq : (1 : PhysicalTensor) - mixtureTensor t =
      (1 - t) • (1 - phaseZero) + t • (1 - phaseOne rho) := by
    unfold mixtureTensor
    module
  rw [heq]
  exact (phaseZero_upper.smul (sub_nonneg.mpr ht.2)).add (phaseOne_upper.smul ht.1)

theorem mixture_posSemidef {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (mixtureTensor t).PosSemidef := by
  have h := (mixture_lower ht).add
    (Matrix.PosSemidef.one.smul (R := ℝ) (n := Fin 2 × Fin 16)
      (show (0 : ℝ) ≤ 1 / 4 by norm_num))
  simpa only [sub_add_cancel] using h

theorem mixture_opNorm_le {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (mixtureTensor t)‖ ≤ 1 := by
  exact Fourier.euclidean_norm_le_of_psd_bound zero_le_one (mixture_posSemidef ht)
    (by simpa only [one_smul] using mixture_upper ht)

end HierarchicalLaminates.Material
