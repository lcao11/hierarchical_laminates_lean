module

public import HierarchicalLaminates.TwoWell.Rotation

/-! Regularity, degree-two homogeneity, and competition of the quadratic branches. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.TwoWell

open Matrix HierarchicalLaminates HierarchicalLaminates.Lamination

theorem phaseZero_posDef : phaseZero.PosDef :=
  materialFamily_posDef rho_pos.le rho_lt_two_thirds
    (phaseZero_mem_materialFamily rho_pos.le)

theorem phaseOne_posDef : (phaseOne rho).PosDef :=
  materialFamily_posDef rho_pos.le rho_lt_two_thirds
    (phaseOne_mem_materialFamily rho_pos.le)

theorem pairedEnergy_continuous (A : Tensor16) : Continuous (pairedEnergy A) := by
  unfold pairedEnergy quadraticEnergy dotProduct Matrix.mulVec
  fun_prop

theorem twoWellEnergy_nonneg (F : PairedGradient) : 0 ≤ twoWellEnergy F :=
  le_min (pairedEnergy_nonneg phaseZero_posDef F) (pairedEnergy_nonneg phaseOne_posDef F)

theorem twoWellEnergy_continuous : Continuous twoWellEnergy :=
  (pairedEnergy_continuous phaseZero).min (pairedEnergy_continuous (phaseOne rho))

theorem twoWellEnergy_homogeneous (r : ℝ) (F : PairedGradient) :
    twoWellEnergy (r • F) = r^2*twoWellEnergy F := by
  unfold twoWellEnergy wellZero wellOne
  rw [pairedEnergy_homogeneous,pairedEnergy_homogeneous,
    mul_min_of_nonneg _ _ (sq_nonneg r)]

theorem xi_phase_energy_strict :
    quadraticEnergy (phaseOne rho) xiFlat < quadraticEnergy phaseZero xiFlat := by
  rw [phaseOne,phaseZero,materialTensor_xi_energy,materialTensor_xi_energy]
  simp only [Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,ite_true,mul_one,
    Matrix.zero_apply,sub_zero]
  linarith [rho_pos]

theorem complementary_fenchel_bound {A : Tensor16} (hA : A.PosDef) (f p : Gradient16) :
    2*(f ⬝ᵥ p) ≤ quadraticEnergy A f+quadraticEnergy A⁻¹ p := by
  have hs := complete_square hA p f
  have hnon : 0 ≤ quadraticEnergy A (f-A⁻¹ *ᵥ p) :=
    hA.posSemidef.dotProduct_mulVec_nonneg _
  change quadraticEnergy A f-2*(f ⬝ᵥ p) =
    quadraticEnergy A (f-A⁻¹ *ᵥ p)-quadraticEnergy A⁻¹ p at hs
  linarith

theorem wellOne_lt_wellZero_primal : wellOne (xiFlat,0) < wellZero (xiFlat,0) := by
  simpa [wellOne,wellZero,pairedEnergy,quadraticEnergy] using xi_phase_energy_strict

theorem wellZero_lt_wellOne_complementary :
    wellZero (0,rotate (phaseZero *ᵥ xiFlat)) <
      wellOne (0,rotate (phaseZero *ᵥ xiFlat)) := by
  have hfenchel := complementary_fenchel_bound phaseOne_posDef
    xiFlat (phaseZero *ᵥ xiFlat)
  have hzero : wellZero (0,rotate (phaseZero *ᵥ xiFlat)) =
      quadraticEnergy phaseZero xiFlat := by
    unfold wellZero pairedEnergy
    rw [dual_energy_flux phaseZero_posDef]
    simp [quadraticEnergy]
  have hone : wellOne (0,rotate (phaseZero *ᵥ xiFlat)) =
      quadraticEnergy (phaseOne rho)⁻¹ (phaseZero *ᵥ xiFlat) := by
    unfold wellOne pairedEnergy
    rw [dual_quadratic_rotate]
    simp [quadraticEnergy]
  rw [hzero,hone]
  change 2*quadraticEnergy phaseZero xiFlat ≤ _ at hfenchel
  linarith [xi_phase_energy_strict]

/-- Each branch is strictly preferred at some gradient, with the same two phases. -/
theorem branches_nondominating :
    (∃ F : PairedGradient, wellOne F < wellZero F) ∧
      (∃ F : PairedGradient, wellZero F < wellOne F) :=
  ⟨⟨(xiFlat,0),wellOne_lt_wellZero_primal⟩,
    ⟨(0,rotate (phaseZero *ᵥ xiFlat)),wellZero_lt_wellOne_complementary⟩⟩

end HierarchicalLaminates.TwoWell
