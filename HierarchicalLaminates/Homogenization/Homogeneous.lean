module

public import HierarchicalLaminates.Material.Arrangements

/-!
# Homogeneous arrangements and their effective tensors

For a constant constitutive law, each constant loading solves the cell
problem because its flux is orthogonal to zero-mean weak gradients. The two
binary endpoint arrangements realize the constituent tensors at fractions
zero and one.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Homogenization

open Matrix MeasureTheory HierarchicalLaminates HierarchicalLaminates.Periodic
  HierarchicalLaminates.Analysis HierarchicalLaminates.Lamination HierarchicalLaminates.Material

def constantFraction (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : PhaseFraction where
  value := fun _ => t
  measurable := measurable_const
  lower := fun _ => ht.1
  upper := fun _ => ht.2

@[simp]
theorem constantFraction_value (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (q : Domain) :
    (constantFraction t ht).value q = t := rfl

theorem constantFraction_mean (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (∫ q, (constantFraction t ht).value q ∂domainMeasure) = t := by
  simp [constantFraction, measureReal_def]

theorem constantFraction_coefficientOperator (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (q : Domain) :
    coefficientOperator (constantFraction t ht) q =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (mixtureTensor t) := by
  exact coefficientOperator_eq_matrix (constantFraction t ht) q

theorem constantFraction_constant_flux (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (F : PhysicalGradient) :
    coefficientLaw (constantFraction t ht) (constantField F) =
      constantField (Matrix.toEuclideanCLM (𝕜 := ℝ) (mixtureTensor t) F) := by
  apply Lp.ext
  filter_upwards [coefficientLaw_coe (constantFraction t ht) (constantField F),
    Lp.coeFn_const 2 domainMeasure F,
    Lp.coeFn_const 2 domainMeasure
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (mixtureTensor t) F)] with q hcoeff hconst hflux
  change constantField F q = F at hconst
  change constantField (Matrix.toEuclideanCLM (𝕜 := ℝ) (mixtureTensor t) F) q =
    Matrix.toEuclideanCLM (𝕜 := ℝ) (mixtureTensor t) F at hflux
  rw [hcoeff, hconst, hflux, constantFraction_coefficientOperator]

theorem constantFraction_constant_isCellField (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (F : PhysicalGradient) :
    IsCellField gradientSpace (coefficientLaw (constantFraction t ht))
      (constantField F) (constantField F) := by
  constructor
  · simpa only [sub_self] using gradientSpace.zero_mem
  · intro g hg
    rw [constantFraction_constant_flux, constant_mean_pairing,
      gradientSpace_mean_zero g hg, inner_zero_right]

theorem constantFraction_cellField (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (F : PhysicalGradient) :
    cellField gradientSpace (coefficientLaw (constantFraction t ht)) (1 / 4)
      (by norm_num) (coefficientLaw_coercive (constantFraction t ht))
      (constantField F) = constantField F := by
  exact cellField_unique (by norm_num : (0 : ℝ) < 1 / 4)
    (coefficientLaw_coercive (constantFraction t ht))
    (cellField_isCellField _ _ _ _ _ _)
    (constantFraction_constant_isCellField t ht F)

theorem constantFraction_effectiveOperator (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (F : PhysicalGradient) :
    HierarchicalLaminates.Material.effectiveOperator (constantFraction t ht) F =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (mixtureTensor t) F := by
  change meanField (coefficientLaw (constantFraction t ht)
    (cellField gradientSpace (coefficientLaw (constantFraction t ht)) (1 / 4)
      (by norm_num) (coefficientLaw_coercive (constantFraction t ht))
      (constantField F))) = _
  rw [constantFraction_cellField, constantFraction_constant_flux, mean_constantField]

theorem effectiveMatrix_constantFraction (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    effectiveMatrix (constantFraction t ht) = mixtureTensor t := by
  apply (Matrix.toEuclideanCLM (𝕜 := ℝ)).injective
  change Matrix.toEuclideanCLM (𝕜 := ℝ) (effectiveMatrix (constantFraction t ht)) =
    Matrix.toEuclideanCLM (𝕜 := ℝ) (mixtureTensor t)
  rw [effectiveMatrix_operator]
  apply ContinuousLinearMap.ext
  intro F
  exact constantFraction_effectiveOperator t ht F

def zeroFraction : PhaseFraction := constantFraction 0 (by norm_num)

def oneFraction : PhaseFraction := constantFraction 1 (by norm_num)

theorem zeroFraction_binary (q : Domain) :
    zeroFraction.value q = 0 ∨ zeroFraction.value q = 1 := Or.inl rfl

theorem oneFraction_binary (q : Domain) :
    oneFraction.value q = 0 ∨ oneFraction.value q = 1 := Or.inr rfl

theorem zeroFraction_mean : (∫ q, zeroFraction.value q ∂domainMeasure) = 0 :=
  constantFraction_mean 0 _

theorem oneFraction_mean : (∫ q, oneFraction.value q ∂domainMeasure) = 1 :=
  constantFraction_mean 1 _

theorem effectiveMatrix_zeroFraction : effectiveMatrix zeroFraction = phaseZero := by
  rw [zeroFraction, effectiveMatrix_constantFraction, mixtureTensor_zero]

theorem effectiveMatrix_oneFraction : effectiveMatrix oneFraction = phaseOne rho := by
  rw [oneFraction, effectiveMatrix_constantFraction, mixtureTensor_one]

end HierarchicalLaminates.Homogenization
