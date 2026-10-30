module

public import HierarchicalLaminates.TwoWell.PeriodicFields
public import HierarchicalLaminates.TwoWell.Rotation

/-! Integral paired energy for one shared binary phase indicator. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.TwoWell

open MeasureTheory Matrix HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.WeakCalculus
  HierarchicalLaminates.Analysis HierarchicalLaminates.Material HierarchicalLaminates.Lamination HierarchicalLaminates.Composition

def matrixMixtureLaw (A₀ A₁ : Tensor16) (b : PhaseFraction) :
    PhysicalField →L[ℝ] PhysicalField :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) A₀).compLpL 2 domainMeasure +
    (scalarMultiplication b.bounded).comp
      ((Matrix.toEuclideanCLM (𝕜 := ℝ) A₁ -
        Matrix.toEuclideanCLM (𝕜 := ℝ) A₀).compLpL 2 domainMeasure)

theorem matrixMixtureLaw_coe (A₀ A₁ : Tensor16) (b : PhaseFraction) (f : PhysicalField) :
    matrixMixtureLaw A₀ A₁ b f =ᵐ[domainMeasure] fun q =>
      Matrix.toEuclideanCLM (𝕜 := ℝ) (A₀+b.value q • (A₁-A₀)) (f q) := by
  let A := Matrix.toEuclideanCLM (𝕜 := ℝ) A₀
  let B := Matrix.toEuclideanCLM (𝕜 := ℝ) A₁
  filter_upwards [Lp.coeFn_add (A.compLpL 2 domainMeasure f)
      (scalarMultiplication b.bounded ((B-A).compLpL 2 domainMeasure f)),
    A.coeFn_compLpL f, scalarMultiplication_coe b.bounded
      ((B-A).compLpL 2 domainMeasure f), (B-A).coeFn_compLpL f]
      with q hadd hA hs hB
  change (A.compLpL 2 domainMeasure f +
    scalarMultiplication b.bounded ((B-A).compLpL 2 domainMeasure f)) q = _
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hA,hs,hB]
  simp only [map_add,map_smul,map_sub,_root_.add_apply,
    _root_.smul_apply,_root_.sub_apply]
  rfl

def dualCoefficientLaw (b : PhaseFraction) : PhysicalField →L[ℝ] PhysicalField :=
  matrixMixtureLaw (dual phaseZero) (dual (phaseOne rho)) b

theorem dualCoefficientLaw_coe (b : PhaseFraction)
    (hb : ∀ q, b.value q = 0 ∨ b.value q = 1) (f : PhysicalField) :
    dualCoefficientLaw b f =ᵐ[domainMeasure] fun q =>
      Matrix.toEuclideanCLM (𝕜 := ℝ) (dual (mixtureTensor (b.value q))) (f q) := by
  filter_upwards [matrixMixtureLaw_coe (dual phaseZero) (dual (phaseOne rho)) b f]
    with q hq
  change dualCoefficientLaw b f q = _ at hq
  rw [hq]
  rcases hb q with h | h
  · simp [h,mixtureTensor_zero]
  · simp [h,mixtureTensor_one]

def selectedPairEnergy (b : PhaseFraction) (e g : PhysicalField) : ℝ :=
  inner ℝ (coefficientLaw b e) e + inner ℝ (dualCoefficientLaw b g) g

theorem fixedPairEnergy_integrable (A : Tensor16) (e g : PhysicalField) :
    Integrable (fun q => pairedEnergy A ((e q : Gradient16),(g q : Gradient16))) domainMeasure := by
  let a := Matrix.toEuclideanCLM (𝕜 := ℝ) A
  let d := Matrix.toEuclideanCLM (𝕜 := ℝ) (dual A)
  apply ((L2.integrable_inner (a.compLpL 2 domainMeasure e) e).add
    (L2.integrable_inner (d.compLpL 2 domainMeasure g) g)).congr
  filter_upwards [a.coeFn_compLpL e,d.coeFn_compLpL g] with q he hg
  change inner ℝ (a.compLpL 2 domainMeasure e q) (e q) +
    inner ℝ (d.compLpL 2 domainMeasure g q) (g q) = _
  rw [he,hg]
  simp only [a,d,pairedEnergy,quadraticEnergy,real_inner_comm,
    Matrix.inner_toEuclideanCLM]

theorem twoWellEnergy_integrable_fields (e g : PhysicalField) :
    Integrable (fun q => twoWellEnergy ((e q : Gradient16),(g q : Gradient16))) domainMeasure :=
  (fixedPairEnergy_integrable phaseZero e g).inf
    (fixedPairEnergy_integrable (phaseOne rho) e g)

theorem selectedPairEnergy_continuous (b : PhaseFraction) :
    Continuous (fun z : PhysicalField × PhysicalField => selectedPairEnergy b z.1 z.2) :=
  ((coefficientLaw b).continuous.comp continuous_fst).inner continuous_fst |>.add
    (((dualCoefficientLaw b).continuous.comp continuous_snd).inner continuous_snd)

theorem selectedPairEnergy_shift_continuous (b : PhaseFraction)
    (f p : PhysicalField) :
    Continuous (fun z : PhysicalField × PhysicalField =>
      selectedPairEnergy b (f+z.1) (p+z.2)) := by
  have hf : Continuous (fun z : PhysicalField × PhysicalField => f+z.1) :=
    continuous_const.add continuous_fst
  have hp : Continuous (fun z : PhysicalField × PhysicalField => p+z.2) :=
    continuous_const.add continuous_snd
  exact (((coefficientLaw b).continuous.comp hf).inner hf).add
    (((dualCoefficientLaw b).continuous.comp hp).inner hp)

theorem selectedPairEnergy_integrable (b : PhaseFraction)
    (hb : ∀ q, b.value q = 0 ∨ b.value q = 1) (e g : PhysicalField) :
    Integrable (fun q => pairedEnergy (mixtureTensor (b.value q))
      ((e q : Gradient16),(g q : Gradient16))) domainMeasure := by
  apply ((L2.integrable_inner (coefficientLaw b e) e).add
    (L2.integrable_inner (dualCoefficientLaw b g) g)).congr
  filter_upwards [coefficientLaw_coe b e,dualCoefficientLaw_coe b hb g] with q he hg
  change inner ℝ (coefficientLaw b e q) (e q) +
    inner ℝ (dualCoefficientLaw b g q) (g q) = _
  rw [he,hg,coefficientOperator_eq_matrix]
  simp only [pairedEnergy,quadraticEnergy,real_inner_comm,
    Matrix.inner_toEuclideanCLM]

theorem selectedPairEnergy_eq_integral (b : PhaseFraction)
    (hb : ∀ q, b.value q = 0 ∨ b.value q = 1) (e g : PhysicalField) :
    selectedPairEnergy b e g = ∫ q,
      pairedEnergy (mixtureTensor (b.value q)) ((e q : Gradient16),(g q : Gradient16)) ∂domainMeasure := by
  rw [selectedPairEnergy,L2.inner_def,L2.inner_def,← integral_add
    (L2.integrable_inner (coefficientLaw b e) e)
    (L2.integrable_inner (dualCoefficientLaw b g) g)]
  apply integral_congr_ae
  filter_upwards [coefficientLaw_coe b e,dualCoefficientLaw_coe b hb g] with q he hg
  rw [he,hg,coefficientOperator_eq_matrix]
  simp only [pairedEnergy,quadraticEnergy,real_inner_comm,
    Matrix.inner_toEuclideanCLM]

theorem selectedPairEnergy_exact_fields (b : PhaseFraction)
    (hb : ∀ q, b.value q = 0 ∨ b.value q = 1) (f η : PhysicalGradient) :
    selectedPairEnergy b (exactCellField b f)
      (rotateField (coefficientLaw b (exactCellField b η))) =
      quadraticEnergy (effectiveMatrix b) (f : Gradient16) +
        quadraticEnergy (effectiveMatrix b) (η : Gradient16) := by
  rw [selectedPairEnergy,exactCellField_energy]
  congr 1
  rw [←exactCellField_energy b η,L2.inner_def,coefficientLaw_energy]
  apply integral_congr_ae
  let e := exactCellField b η
  filter_upwards [dualCoefficientLaw_coe b hb (rotateField (coefficientLaw b e)),
    (rotatePhysical.coeFn_compLpL (coefficientLaw b e)),coefficientLaw_coe b e]
    with q hd hr hc
  rw [← rotateField_eq_lift] at hr
  rw [hd,hr,hc,coefficientOperator_eq_matrix]
  rw [real_inner_comm,Matrix.inner_toEuclideanCLM]
  have haction : (Matrix.toEuclideanCLM (𝕜 := ℝ)
      (mixtureTensor (b.value q)) (e q) : Gradient16) =
      mixtureTensor (b.value q) *ᵥ (e q : Gradient16) := rfl
  rw [rotatePhysical_apply,haction]
  have hpos : (mixtureTensor (b.value q)).PosDef := by
    rcases hb q with hz | ho
    · rw [hz,mixtureTensor_zero]
      exact materialFamily_posDef rho_pos.le rho_lt_two_thirds
        (phaseZero_mem_materialFamily rho_pos.le)
    · rw [ho,mixtureTensor_one]
      exact materialFamily_posDef rho_pos.le rho_lt_two_thirds
        (phaseOne_mem_materialFamily rho_pos.le)
  simpa only [quadraticEnergy,e,real_inner_comm,Matrix.inner_toEuclideanCLM]
    using dual_energy_flux hpos (e q : Gradient16)

end HierarchicalLaminates.TwoWell
