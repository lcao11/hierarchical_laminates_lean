module

public import HierarchicalLaminates.Material.Arrangements

/-!
# Periodic coefficient laws with variable contrast

For contrast `r` and a measurable phase parameter `b` taking values in `[0, 1]`,
the coefficient law is the pointwise mixture of `phaseZero` and `phaseOne r`.
When `0 ≤ r < 2 / 3`, its ellipticity constant is
`min (1 / 4) (1 - 3 * r / 2)` and its operator norm is at most one.

The effective operator is identified with the weak-H¹ cell energy for every
loading. `physicalGap r` is the difference between the two selected loading
energies for the smooth periodic arrangement `smoothFraction`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.Contrast

open Matrix MeasureTheory Periodic Material Lamination Analysis

/-- A common lower bound for the vertical and horizontal coefficient blocks. -/
def ellipticity (r : ℝ) : ℝ := min (1 / 4) (1 - 3 * r / 2)

theorem ellipticity_pos {r : ℝ} (hr : r < 2 / 3) : 0 < ellipticity r := by
  unfold ellipticity
  apply lt_min (by norm_num)
  linarith

theorem ellipticity_eq_quarter {r : ℝ} (hr : r ≤ 1/3) : ellipticity r = 1/4 := by
  apply min_eq_left
  linarith

def mixtureTensor (r t : ℝ) : PhysicalTensor := materialTensor ((r * t) • (1 : RMatrix8))

theorem mixtureTensor_affine (r t : ℝ) :
    mixtureTensor r t = phaseZero + t • (phaseOne r - phaseZero) := by
  have h := materialTensor_average (r • (1 : RMatrix8)) 0 t
  simp only [matrixAverage, smul_zero, add_zero, smul_smul] at h
  change mixtureTensor r t = _
  rw [mixtureTensor, mul_comm r t, ← h]
  unfold phaseOne phaseZero
  module

theorem horizontal_lower {r c : ℝ} (hr : 0 ≤ r) (hc : c ≤ 1 - 3 * r / 2) :
    (horizontalR (r • (1 : RMatrix8)) - c • (1 : Matrix (Fin 16) (Fin 16) ℝ)).PosSemidef := by
  have heq : horizontalR (r • (1 : RMatrix8)) - c • (1 : Matrix (Fin 16) (Fin 16) ℝ) =
      (1-c-(3/2 : ℝ)*r) • 1 + r • ((3/2 : ℝ) • 1 - factorR * factorRᵀ) := by
    simp only [horizontalR, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      smul_sub, smul_smul]
    module
  rw [heq]
  exact (Matrix.PosSemidef.one.smul (by linarith)).add (factorR_upper_posSemidef.smul hr)

theorem mixture_lower {r t : ℝ} (hr : 0 ≤ r) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (mixtureTensor r t - ellipticity r • (1 : PhysicalTensor)).PosSemidef := by
  have hrt : r*t ≤ r := by nlinarith [ht.2]
  rw [mixtureTensor, materialTensor_eq_spatialBlocks, spatialBlocks_sub_identity]
  apply spatialBlocks_posSemidef
  · apply horizontal_lower (mul_nonneg hr ht.1)
    have hm := min_le_right (1/4 : ℝ) (1-3*r/2)
    change ellipticity r ≤ _
    unfold ellipticity
    linarith
  · have hm := min_le_left (1/4 : ℝ) (1-3*r/2)
    have heq : verticalR - ellipticity r • (1 : Matrix (Fin 16) (Fin 16) ℝ) =
        (verticalR-(1/4 : ℝ) • 1) + ((1/4 : ℝ)-ellipticity r) • 1 := by module
    rw [heq]
    exact verticalR_lower_posSemidef.add (Matrix.PosSemidef.one.smul (by
      change 0 ≤ (1/4 : ℝ)-min (1/4 : ℝ) (1-3*r/2)
      linarith))

theorem mixture_upper {r t : ℝ} (hr : 0 ≤ r) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ((1 : PhysicalTensor) - mixtureTensor r t).PosSemidef := by
  rw [mixtureTensor, materialTensor_eq_spatialBlocks, identity_sub_spatialBlocks]
  exact spatialBlocks_posSemidef
    (horizontalR_upper_posSemidef (Matrix.PosSemidef.one.smul (mul_nonneg hr ht.1)))
    verticalR_upper_posSemidef

theorem mixture_posSemidef {r t : ℝ} (hr : 0 ≤ r) (hrlt : r < 2/3)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : (mixtureTensor r t).PosSemidef := by
  have h := (mixture_lower hr ht).add (Matrix.PosSemidef.one.smul
    (R := ℝ) (n := Fin 2 × Fin 16) (ellipticity_pos hrlt).le)
  simpa only [sub_add_cancel] using h

def onePhaseOperator (r : ℝ) : PhysicalGradient →L[ℝ] PhysicalGradient :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (phaseOne r)

def coefficientOperator (r : ℝ) (b : PhaseFraction) (q : Domain) :
    PhysicalGradient →L[ℝ] PhysicalGradient :=
  zeroPhaseOperator + b.value q • (onePhaseOperator r - zeroPhaseOperator)

theorem coefficientOperator_eq_matrix (r : ℝ) (b : PhaseFraction) (q : Domain) :
    coefficientOperator r b q = Matrix.toEuclideanCLM (𝕜 := ℝ) (mixtureTensor r (b.value q)) := by
  rw [mixtureTensor_affine]
  simp only [map_add, map_smul, map_sub]
  rfl

def coefficientLaw (r : ℝ) (b : PhaseFraction) : PhysicalField →L[ℝ] PhysicalField :=
  zeroPhaseOperator.compLpL 2 domainMeasure +
    (scalarMultiplication b.bounded).comp
      ((onePhaseOperator r - zeroPhaseOperator).compLpL 2 domainMeasure)

theorem coefficientLaw_coe (r : ℝ) (b : PhaseFraction) (f : PhysicalField) :
    coefficientLaw r b f =ᵐ[domainMeasure] fun q => coefficientOperator r b q (f q) := by
  change ((zeroPhaseOperator.compLpL 2 domainMeasure f) +
    scalarMultiplication b.bounded
      ((onePhaseOperator r-zeroPhaseOperator).compLpL 2 domainMeasure f)) =ᵐ[domainMeasure] _
  filter_upwards [Lp.coeFn_add (zeroPhaseOperator.compLpL 2 domainMeasure f)
      (scalarMultiplication b.bounded ((onePhaseOperator r-zeroPhaseOperator).compLpL 2 domainMeasure f)),
    zeroPhaseOperator.coeFn_compLpL f,
    scalarMultiplication_coe b.bounded ((onePhaseOperator r-zeroPhaseOperator).compLpL 2 domainMeasure f),
    (onePhaseOperator r-zeroPhaseOperator).coeFn_compLpL f] with q hadd hz hs hd
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hz,hs,hd]
  rfl

theorem coefficientOperator_lower {r : ℝ} (hr : 0 ≤ r) (b : PhaseFraction)
    (q : Domain) (v : PhysicalGradient) :
    ellipticity r * inner ℝ v v ≤ inner ℝ (coefficientOperator r b q v) v := by
  rw [coefficientOperator_eq_matrix]
  have hpsd := mixture_lower hr (show b.value q ∈ Set.Icc (0 : ℝ) 1 from ⟨b.lower q,b.upper q⟩)
  have h : 0 ≤ inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ)
      (mixtureTensor r (b.value q)-ellipticity r • (1 : PhysicalTensor)) v) := by
    simpa only [Matrix.inner_toEuclideanCLM,star_trivial] using
      hpsd.dotProduct_mulVec_nonneg (v : Fin 2 × Fin 16 → ℝ)
  simp only [map_sub,map_smul,map_one,_root_.sub_apply,_root_.smul_apply,
    one_apply_eq_self,inner_sub_right,inner_smul_right] at h
  linarith [real_inner_comm v (Matrix.toEuclideanCLM (𝕜 := ℝ) (mixtureTensor r (b.value q)) v)]

theorem coefficientLaw_coercive {r : ℝ} (hr : 0 ≤ r) (b : PhaseFraction) :
    CoerciveLaw (coefficientLaw r b) (ellipticity r) :=
  fieldLaw_coercive _ _ (coefficientLaw_coe r b) _ (coefficientOperator_lower hr b)

theorem coefficientOperator_symmetric {r : ℝ} (hr : 0 ≤ r) (hrlt : r < 2/3)
    (b : PhaseFraction) (q : Domain) (v w : PhysicalGradient) :
    inner ℝ (coefficientOperator r b q v) w = inner ℝ v (coefficientOperator r b q w) := by
  have hsym : (coefficientOperator r b q).IsSymmetric := by
    rw [coefficientOperator_eq_matrix]
    change (Matrix.toEuclideanCLM (𝕜 := ℝ) (mixtureTensor r (b.value q)) :
      PhysicalGradient →ₗ[ℝ] PhysicalGradient).IsSymmetric
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (mixture_posSemidef hr hrlt ⟨b.lower q,b.upper q⟩).isHermitian
  exact hsym v w

theorem coefficientLaw_symmetric {r : ℝ} (hr : 0 ≤ r) (hrlt : r < 2/3) (b : PhaseFraction) :
    SymmetricLaw (coefficientLaw r b) :=
  fieldLaw_symmetric _ _ (coefficientLaw_coe r b) (coefficientOperator_symmetric hr hrlt b)

theorem coefficientOperator_bound {r : ℝ} (hr : 0 ≤ r) (hrlt : r < 2/3)
    (b : PhaseFraction) (q : Domain) (v : PhysicalGradient) :
    ‖coefficientOperator r b q v‖ ≤ ‖v‖ := by
  rw [coefficientOperator_eq_matrix]
  have hn : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (mixtureTensor r (b.value q))‖ ≤ 1 :=
    Fourier.euclidean_norm_le_of_psd_bound zero_le_one
      (mixture_posSemidef hr hrlt ⟨b.lower q,b.upper q⟩)
      (by simpa only [one_smul] using mixture_upper hr ⟨b.lower q,b.upper q⟩)
  exact ((Matrix.toEuclideanCLM (𝕜 := ℝ) (mixtureTensor r (b.value q))).le_opNorm v).trans
    (by simpa using mul_le_mul_of_nonneg_right hn (norm_nonneg v))

theorem coefficientLaw_norm_le {r : ℝ} (hr : 0 ≤ r) (hrlt : r < 2/3)
    (b : PhaseFraction) (f : PhysicalField) : ‖coefficientLaw r b f‖ ≤ ‖f‖ := by
  have hb : ∀ q v,‖coefficientOperator r b q v‖ ≤ 1*‖v‖ := by
    intro q v
    simpa only [one_mul] using coefficientOperator_bound hr hrlt b q v
  simpa only [one_mul] using fieldLaw_norm_bound _ _ (coefficientLaw_coe r b) 1 hb f

def effectiveOperator (r : ℝ) (hr : 0 ≤ r) (hrlt : r < 2/3) (b : PhaseFraction) :
    PhysicalGradient →L[ℝ] PhysicalGradient :=
  periodicEffective (coefficientLaw r b) (ellipticity r) (ellipticity_pos hrlt)
    (coefficientLaw_coercive hr b)

def effectiveMatrix (r : ℝ) (hr : 0 ≤ r) (hrlt : r < 2/3) (b : PhaseFraction) : PhysicalTensor :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ)).symm (effectiveOperator r hr hrlt b)

theorem effectiveMatrix_operator (r : ℝ) (hr : 0 ≤ r) (hrlt : r < 2/3) (b : PhaseFraction) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (effectiveMatrix r hr hrlt b) = effectiveOperator r hr hrlt b :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ)).apply_symm_apply _

theorem effectiveOperator_cell_energy (r : ℝ) (hr : 0 ≤ r) (hrlt : r < 2/3)
    (b : PhaseFraction) (F : PhysicalGradient) :
    inner ℝ (effectiveOperator r hr hrlt b F) F = sobolevCellEnergy (coefficientLaw r b) F :=
  periodicEffective_energy _ (coefficientLaw_symmetric hr hrlt b) _ _ _ F

theorem effectiveMatrix_quadratic_energy (r : ℝ) (hr : 0 ≤ r) (hrlt : r < 2/3)
    (b : PhaseFraction) (F : PhysicalGradient) :
    quadraticEnergy (effectiveMatrix r hr hrlt b) (F : Fin 2 × Fin 16 → ℝ) =
      sobolevCellEnergy (coefficientLaw r b) F := by
  have h := effectiveOperator_cell_energy r hr hrlt b F
  rw [← effectiveMatrix_operator r hr hrlt b] at h
  have hi := Matrix.inner_toEuclideanCLM (effectiveMatrix r hr hrlt b) F F
  change inner ℝ F (Matrix.toEuclideanCLM (𝕜 := ℝ) (effectiveMatrix r hr hrlt b) F) =
    quadraticEnergy (effectiveMatrix r hr hrlt b) (F : Fin 2 × Fin 16 → ℝ) at hi
  linarith [real_inner_comm F (Matrix.toEuclideanCLM (𝕜 := ℝ) (effectiveMatrix r hr hrlt b) F)]

theorem coefficientLaw_rho (b : PhaseFraction) :
    coefficientLaw rho b = Material.coefficientLaw b := rfl

/-- The selected weak-H¹ cell-energy difference for `smoothFraction`.
The formula is defined for every real `r`; its coercive physical interpretation
and subsequent response identities use `0 ≤ r < 2 / 3`. -/
def physicalGap (r : ℝ) : ℝ :=
  sobolevCellEnergy (coefficientLaw r smoothFraction) (WithLp.toLp 2 etaFlat) -
    sobolevCellEnergy (coefficientLaw r smoothFraction) (WithLp.toLp 2 xiFlat)

end HierarchicalLaminates.Contrast
