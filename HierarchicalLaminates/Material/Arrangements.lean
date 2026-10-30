module

public import HierarchicalLaminates.Material.CoefficientLaw
public import HierarchicalLaminates.Binary.Geometry
public import HierarchicalLaminates.Fourier.CosineProfile
public import HierarchicalLaminates.Lamination.PhysicalLamination

/-! Concrete smooth and binary arrangements of the same prescribed phases. -/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Material

open HierarchicalLaminates.Periodic HierarchicalLaminates.Lamination

def smoothFraction : PhaseFraction where
  value := Fourier.cosineProfile
  measurable := Fourier.cosineProfile.continuous.measurable
  lower := Fourier.cosineProfile_nonneg
  upper := Fourier.cosineProfile_le_one

def binaryFraction (N : ℕ) : PhaseFraction where
  value := Binary.binaryIndicator N
  measurable := Binary.binaryIndicator_measurable N
  lower := fun q => (Binary.binaryIndicator_mem N q).1
  upper := fun q => (Binary.binaryIndicator_mem N q).2

theorem binaryFraction_values (N : ℕ) (q : Domain) :
    (binaryFraction N).value q = 0 ∨ (binaryFraction N).value q = 1 :=
  Binary.binaryIndicator_values N q

theorem mixtureTensor_zero : mixtureTensor 0 = phaseZero := by
  simp [mixtureTensor]

theorem mixtureTensor_one : mixtureTensor 1 = phaseOne rho := by
  simp [mixtureTensor]

theorem binary_coefficient_values (N : ℕ) (q : Domain) :
    mixtureTensor ((binaryFraction N).value q) = phaseZero ∨
      mixtureTensor ((binaryFraction N).value q) = phaseOne rho := by
  rcases binaryFraction_values N q with h | h
  · exact Or.inl (h ▸ mixtureTensor_zero)
  · exact Or.inr (h ▸ mixtureTensor_one)

theorem effectiveMatrix_quadratic_energy (b : PhaseFraction) (F : PhysicalGradient) :
    quadraticEnergy (effectiveMatrix b) (F : Fin 2 × Fin 16 → ℝ) =
      sobolevCellEnergy (coefficientLaw b) F := by
  have h := effectiveOperator_cell_energy b F
  rw [← effectiveMatrix_operator b] at h
  have hinner := Matrix.inner_toEuclideanCLM (effectiveMatrix b) F F
  change inner ℝ F (Matrix.toEuclideanCLM (𝕜 := ℝ) (effectiveMatrix b) F) =
    quadraticEnergy (effectiveMatrix b) (F : Fin 2 × Fin 16 → ℝ) at hinner
  linarith [real_inner_comm F
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (effectiveMatrix b) F)]

def physicalLoadingDifference (b : PhaseFraction) : ℝ :=
  loadingDifference xiFlat etaFlat (effectiveMatrix b)

/-- A positive binary loading difference separates the effective tensor
from the closure of all finite laminate hierarchies. -/
theorem binary_positive_excludes_all_laminate_limits (N : ℕ)
    (hpositive : 0 < physicalLoadingDifference (binaryFraction N)) :
    effectiveMatrix (binaryFraction N) ∉
      closure (allFiniteLaminates phaseZero (phaseOne rho)) := by
  exact positive_loading_difference_not_in_laminateClosure
    (le_of_lt rho_pos) rho_lt_two_thirds hpositive

end HierarchicalLaminates.Material
