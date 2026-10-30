module

public import HierarchicalLaminates.Contrast.CellIdentification
public import HierarchicalLaminates.Homogenization.EffectiveBlocks

/-!
# Full effective tensor at variable contrast

For `0 ≤ r < 2 / 3`, the effective matrix of `smoothFraction` is
`materialTensor (meanResponseMatrix r)`. The proof uses every horizontal basis
loading and the common vertical columns, so the identity covers the whole
tensor. Vertical constant fields solve the cell problem for any admissible
phase parameter `b`.

`meanResponse_tail_five` bounds the reduced mean's remainder after five
Neumann terms in the Euclidean operator norm.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.Contrast

open Matrix MeasureTheory Periodic Material Lamination Analysis Corrector Homogenization Fourier

theorem coefficientOperator_vertical_action (r : ℝ) (b : PhaseFraction) (q : Domain)
    (F : PhysicalGradient) (hF : IsVerticalLoading F) :
    coefficientOperator r b q F = zeroPhaseOperator F := by
  rw [coefficientOperator_eq_matrix]
  exact materialTensor_vertical_action _ F hF

theorem coefficientLaw_constant_vertical (r : ℝ) (b : PhaseFraction)
    (F : PhysicalGradient) (hF : IsVerticalLoading F) :
    coefficientLaw r b (constantField F) = constantField (zeroPhaseOperator F) := by
  apply Lp.ext
  filter_upwards [coefficientLaw_coe r b (constantField F),
    Lp.coeFn_const 2 domainMeasure F,
    Lp.coeFn_const 2 domainMeasure (zeroPhaseOperator F)] with q hc hf hj
  change constantField F q = F at hf
  change constantField (zeroPhaseOperator F) q = zeroPhaseOperator F at hj
  rw [hc,hf,hj]
  exact coefficientOperator_vertical_action r b q F hF

theorem constant_vertical_isCellField (r : ℝ) (b : PhaseFraction)
    (F : PhysicalGradient) (hF : IsVerticalLoading F) :
    IsCellField gradientSpace (coefficientLaw r b) (constantField F) (constantField F) := by
  constructor
  · simpa only [sub_self] using gradientSpace.zero_mem
  · intro g hg
    rw [coefficientLaw_constant_vertical r b F hF,constant_mean_pairing,
      gradientSpace_mean_zero g hg,inner_zero_right]

theorem effectiveOperator_vertical_action {r : ℝ} (hr : 0 ≤ r) (hrlt : r < 2/3)
    (b : PhaseFraction) (F : PhysicalGradient) (hF : IsVerticalLoading F) :
    effectiveOperator r hr hrlt b F = zeroPhaseOperator F := by
  have heq : cellField gradientSpace (coefficientLaw r b) (ellipticity r)
      (ellipticity_pos hrlt) (coefficientLaw_coercive hr b) (constantField F) = constantField F :=
    cellField_unique (ellipticity_pos hrlt) (coefficientLaw_coercive hr b)
      (cellField_isCellField _ _ _ _ _ _) (constant_vertical_isCellField r b F hF)
  change meanField (coefficientLaw r b (cellField gradientSpace (coefficientLaw r b) (ellipticity r)
    (ellipticity_pos hrlt) (coefficientLaw_coercive hr b) (constantField F))) = _
  rw [heq,coefficientLaw_constant_vertical r b F hF,mean_constantField]

theorem effectiveMatrix_isHermitian {r : ℝ} (hr : 0 ≤ r) (hrlt : r < 2/3) (b : PhaseFraction) :
    (effectiveMatrix r hr hrlt b).IsHermitian := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mp
  change (Matrix.toEuclideanCLM (𝕜 := ℝ) (effectiveMatrix r hr hrlt b) :
    PhysicalGradient →ₗ[ℝ] PhysicalGradient).IsSymmetric
  rw [effectiveMatrix_operator]
  exact periodicEffective_symmetric _ (coefficientLaw_symmetric hr hrlt b) _ _ _

theorem effectiveMatrix_vertical_column {r : ℝ} (hr : 0 ≤ r) (hrlt : r < 2/3)
    (b : PhaseFraction) (j : Fin 2 × Fin 16) (a : Fin 16) :
    effectiveMatrix r hr hrlt b j (1,a) = phaseZero j (1,a) := by
  let F : PhysicalGradient := WithLp.toLp 2 (Pi.single (1,a) (1 : ℝ))
  have hF : IsVerticalLoading F := by intro c; simp [F]
  have h := congrArg (fun v : PhysicalGradient => v j)
    (effectiveOperator_vertical_action hr hrlt b F hF)
  rw [← effectiveMatrix_operator r hr hrlt b] at h
  change (effectiveMatrix r hr hrlt b *ᵥ Pi.single (1,a) (1 : ℝ)) j =
    (phaseZero *ᵥ Pi.single (1,a) (1 : ℝ)) j at h
  simpa [Matrix.mulVec,dotProduct,Pi.single_apply] using h

/-- The entire effective matrix of `smoothFraction` has the reduced-tensor
representation for `0 ≤ r < 2 / 3`. -/
theorem effectiveMatrix_eq_materialTensor {r : ℝ} (hr : 0 ≤ r) (hrlt : r < 2/3) :
    effectiveMatrix r hr hrlt smoothFraction = materialTensor (meanResponseMatrix r) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  fin_cases j
  · let z : PotentialVector := WithLp.toLp 2 (Pi.single b (1 : ℝ))
    have hs : (horizontalLoading z : PhysicalIndex → ℝ) = Pi.single (0,b) 1 := by
      ext ⟨k,c⟩
      fin_cases k <;> simp [horizontalLoading,z,Pi.single_apply]
    have h := congrArg (fun F : PhysicalGradient => F (i,a)) (effective_horizontal_operator hr hrlt z)
    rw [← effectiveMatrix_operator r hr hrlt smoothFraction] at h
    change (effectiveMatrix r hr hrlt smoothFraction *ᵥ (horizontalLoading z : PhysicalIndex → ℝ)) (i,a) =
      (materialTensor (meanResponseMatrix r) *ᵥ (horizontalLoading z : PhysicalIndex → ℝ)) (i,a) at h
    rw [hs] at h
    simpa [Matrix.mulVec,dotProduct,Pi.single_apply] using h
  · change effectiveMatrix r hr hrlt smoothFraction (i,a) (1,b) =
      materialTensor (meanResponseMatrix r) (i,a) (1,b)
    rw [effectiveMatrix_vertical_column hr hrlt]
    fin_cases i <;> simp [phaseZero,materialTensor]

/-- An operator-norm remainder bound for the reduced mean representing the
full effective tensor, after the first five Neumann terms. -/
theorem meanResponse_tail_five {r : ℝ} (hr : 0 ≤ r) (hrlt : r < 2/3) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (meanResponseMatrix r) -
      (∑ n ∈ Finset.range 5,neumannTerm (contrastIteration r) (source r) n) (0,0)‖ ≤
      (3/2 : ℝ)^5*r^6/(1-3*r/2) := by
  rw [meanResponseMatrix,(Matrix.toEuclideanCLM (𝕜 := ℝ)).apply_symm_apply]
  exact (lp.norm_apply_le_norm (by norm_num : (1 : ENNReal) ≠ 0)
    (solution r-∑ n ∈ Finset.range 5,neumannTerm (contrastIteration r) (source r) n) (0,0)).trans
      (solution_tail_five hr hrlt)

end HierarchicalLaminates.Contrast
