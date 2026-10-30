module

public import HierarchicalLaminates.TwoWell.Rotation
public import HierarchicalLaminates.GClosure.GeneralLayerAlgebra
public import HierarchicalLaminates.GClosure.GeneralLayerNormal

/-! Planar duality for the variational layer minimum. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.TwoWell

open Matrix HierarchicalLaminates HierarchicalLaminates.Lamination HierarchicalLaminates.GClosure

theorem normalJump_dot (n : LayerNormal) (z : Fin 16 → ℝ) (J : Gradient16) :
    normalJump n z ⬝ᵥ J = z ⬝ᵥ (normalMatrix n)ᵀ *ᵥ J := by
  rw [Matrix.dotProduct_transpose_mulVec, normalMatrix_mulVec, dotProduct_comm]

theorem rotate_normalJump_normal_zero (n : LayerNormal) (z : Fin 16 → ℝ) :
    (normalMatrix n)ᵀ *ᵥ rotate (normalJump n z) = 0 := by
  ext a
  rw [normal_component]
  simp [rotate, normalJump]
  ring

theorem rotate_of_normal_zero (n : LayerNormal) (J : Gradient16)
    (hJ : (normalMatrix n)ᵀ *ᵥ J = 0) :
    rotate J = normalJump n (tangentAmplitude n J) := by
  calc
    rotate J = rotate (tangentField n (tangentAmplitude n J)) :=
      congrArg rotate (tangentField_eq_of_normal_zero n J hJ).symm
    _ = normalJump n (tangentAmplitude n J) := by
      ext ⟨i,a⟩
      fin_cases i <;> simp [rotate, tangentField, normalJump]

theorem layer_fields_of_mean_jump (n : LayerNormal) (a : ℝ)
    (F e₁ e₂ : Gradient16) (z : Fin 16 → ℝ)
    (hmean : a • e₁+(1-a) • e₂ = F) (hjump : e₁-e₂ = normalJump n z) :
    e₁ = firstLayerField n a F z ∧ e₂ = secondLayerField n a F z := by
  rw [← hmean, firstLayerField, secondLayerField, ← hjump]
  constructor <;> module

theorem quadraticEnergy_add_smul {A : Tensor16} (hA : A.IsHermitian)
    (F H : Gradient16) (a : ℝ) :
    quadraticEnergy A (F+a • H) = quadraticEnergy A F+
      2*a*(H ⬝ᵥ A *ᵥ F)+a^2*quadraticEnergy A H :=
  quadratic_add_smul hA F H a

/-- Normal-flux matching is precisely stationarity of the compatible-jump energy. -/
theorem layerEnergy_minimum_of_flux_match {A B : Tensor16}
    (hA : A.PosDef) (hB : B.PosDef) (n : LayerNormal) (a : LayerProportion)
    (F : Gradient16) (z : Fin 16 → ℝ)
    (hmatch : (normalMatrix n)ᵀ *ᵥ (A *ᵥ firstLayerField n (a : ℝ) F z) =
      (normalMatrix n)ᵀ *ᵥ (B *ᵥ secondLayerField n (a : ℝ) F z)) :
    IsLeast (Set.range (layerEnergy A B n (a : ℝ) F))
      (layerEnergy A B n (a : ℝ) F z) := by
  refine ⟨⟨z,rfl⟩, ?_⟩
  rintro v ⟨w,rfl⟩
  let H := normalJump n (w-z)
  have hfirst : firstLayerField n (a : ℝ) F w =
      firstLayerField n (a : ℝ) F z+(1-(a : ℝ)) • H := by
    ext p
    simp [firstLayerField, H, normalJump]
    ring
  have hsecond : secondLayerField n (a : ℝ) F w =
      secondLayerField n (a : ℝ) F z+(-(a : ℝ)) • H := by
    ext p
    simp [secondLayerField, H, normalJump]
    ring
  have hcross : H ⬝ᵥ A *ᵥ firstLayerField n (a : ℝ) F z =
      H ⬝ᵥ B *ᵥ secondLayerField n (a : ℝ) F z := by
    change normalJump n (w-z) ⬝ᵥ _ = normalJump n (w-z) ⬝ᵥ _
    rw [normalJump_dot, normalJump_dot, hmatch]
  have hnonA : 0 ≤ quadraticEnergy A H := hA.posSemidef.dotProduct_mulVec_nonneg H
  have hnonB : 0 ≤ quadraticEnergy B H := hB.posSemidef.dotProduct_mulVec_nonneg H
  have ha := a.property.1
  have hb := sub_nonneg.mpr a.property.2
  have hpA := mul_nonneg (mul_nonneg ha (sq_nonneg (1-(a : ℝ)))) hnonA
  have hpB := mul_nonneg (mul_nonneg hb (sq_nonneg (a : ℝ))) hnonB
  simp only [layerEnergy, hfirst, hsecond,
    quadraticEnergy_add_smul hA.isHermitian, quadraticEnergy_add_smul hB.isHermitian]
  nlinarith

/-- Energy of stationary layer fields equals mean gradient paired with mean flux. -/
theorem layerEnergy_eq_mean_pairing (A B : Tensor16) (n : LayerNormal) (a : ℝ)
    (F : Gradient16) (z : Fin 16 → ℝ)
    (hmatch : (normalMatrix n)ᵀ *ᵥ (A *ᵥ firstLayerField n a F z) =
      (normalMatrix n)ᵀ *ᵥ (B *ᵥ secondLayerField n a F z)) :
    layerEnergy A B n a F z =
      F ⬝ᵥ (a • (A *ᵥ firstLayerField n a F z)+
        (1-a) • (B *ᵥ secondLayerField n a F z)) := by
  have hc : normalJump n z ⬝ᵥ A *ᵥ firstLayerField n a F z =
      normalJump n z ⬝ᵥ B *ᵥ secondLayerField n a F z := by
    rw [normalJump_dot, normalJump_dot, hmatch]
  have he₁ : quadraticEnergy A (firstLayerField n a F z) =
      F ⬝ᵥ A *ᵥ firstLayerField n a F z+
        (1-a)*(normalJump n z ⬝ᵥ A *ᵥ firstLayerField n a F z) := by
    change (F+(1-a) • normalJump n z) ⬝ᵥ _ = _
    rw [add_dotProduct, smul_dotProduct, smul_eq_mul]
  have he₂ : quadraticEnergy B (secondLayerField n a F z) =
      F ⬝ᵥ B *ᵥ secondLayerField n a F z-
        a*(normalJump n z ⬝ᵥ B *ᵥ secondLayerField n a F z) := by
    change (F-a • normalJump n z) ⬝ᵥ _ = _
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul]
  rw [layerEnergy, he₁, he₂, dotProduct_add, dotProduct_smul, dotProduct_smul, hc]
  simp only [smul_eq_mul]
  ring

/-- Layering the complementary duals gives the complementary dual of the layer.
Both layer energies are minimized over all compatible jumps. -/
theorem dual_isLayerTensor {A B D : Tensor16} (hA : A.PosDef) (hB : B.PosDef)
    (hD : D.PosDef) (n : LayerNormal) (a : LayerProportion)
    (hLayer : IsLayerTensor A B n a D) :
    IsLayerTensor (dual A) (dual B) n a (dual D) := by
  have hcomputed : D = computedLayerTensor A B n (a : ℝ) :=
    hLayer.unique (computedLayerTensor_represents_minimum hA hB n a)
  refine ⟨(dual_posDef hD).isHermitian, ?_⟩
  intro g
  let F : Gradient16 := D⁻¹ *ᵥ (-rotate g)
  let e₁ := firstOptimalField A B n (a : ℝ) F
  let e₂ := secondOptimalField A B n (a : ℝ) F
  let j₁ := A *ᵥ e₁
  let j₂ := B *ᵥ e₂
  have hDF : D *ᵥ F = -rotate g := by
    let := hD.isUnit.invertible
    simp [F, Matrix.mulVec_mulVec]
  have hmeanE : (a : ℝ) • e₁+(1-(a : ℝ)) • e₂ = F :=
    optimal_fields_mean A B n (a : ℝ) F
  have hmeanJ : (a : ℝ) • j₁+(1-(a : ℝ)) • j₂ = D *ᵥ F := by
    rw [hcomputed]
    exact optimal_flux_mean hA.isHermitian hB.isHermitian n (a : ℝ) F
  have hnormal : (normalMatrix n)ᵀ *ᵥ j₁ = (normalMatrix n)ᵀ *ᵥ j₂ :=
    optimal_normal_flux_match hA hB n a.property.1 a.property.2 F
  have hdiff : (normalMatrix n)ᵀ *ᵥ (j₁-j₂) = 0 := by
    rw [Matrix.mulVec_sub, hnormal, sub_self]
  let z := tangentAmplitude n (j₁-j₂)
  have hjump : rotate j₁-rotate j₂ = normalJump n z := by
    rw [← rotate_sub]
    exact rotate_of_normal_zero n (j₁-j₂) hdiff
  have hmean : (a : ℝ) • rotate j₁+(1-(a : ℝ)) • rotate j₂ = g := by
    rw [← rotate_smul, ← rotate_smul, ← rotate_add, hmeanJ, hDF,
      ← neg_one_smul ℝ (rotate g), rotate_smul, rotate_rotate]
    simp
  obtain ⟨he₁,he₂⟩ := layer_fields_of_mean_jump n (a : ℝ) g
    (rotate j₁) (rotate j₂) z hmean hjump
  have hdual₁ : dual A *ᵥ firstLayerField n (a : ℝ) g z = rotate e₁ := by
    rw [← he₁]
    exact dual_mul_rotate hA e₁
  have hdual₂ : dual B *ᵥ secondLayerField n (a : ℝ) g z = rotate e₂ := by
    rw [← he₂]
    exact dual_mul_rotate hB e₂
  have hdualnormal : (normalMatrix n)ᵀ *ᵥ (dual A *ᵥ firstLayerField n (a : ℝ) g z) =
      (normalMatrix n)ᵀ *ᵥ (dual B *ᵥ secondLayerField n (a : ℝ) g z) := by
    rw [hdual₁,hdual₂]
    apply sub_eq_zero.mp
    rw [← Matrix.mulVec_sub, ← rotate_sub]
    change (normalMatrix n)ᵀ *ᵥ rotate (firstLayerField n (a : ℝ) F
      (optimalLayerJump A B n (a : ℝ) F)-secondLayerField n (a : ℝ) F
      (optimalLayerJump A B n (a : ℝ) F)) = 0
    rw [layer_fields_jump, rotate_normalJump_normal_zero]
  have hdualmean : (a : ℝ) • (dual A *ᵥ firstLayerField n (a : ℝ) g z)+
      (1-(a : ℝ)) • (dual B *ᵥ secondLayerField n (a : ℝ) g z) = dual D *ᵥ g := by
    rw [hdual₁,hdual₂, ← rotate_smul, ← rotate_smul, ← rotate_add, hmeanE]
    have hd := dual_mul_rotate hD F
    rw [hDF, ← neg_one_smul ℝ (rotate g), rotate_smul, rotate_rotate] at hd
    simpa using hd.symm
  have henergy : layerEnergy (dual A) (dual B) n (a : ℝ) g z =
      quadraticEnergy (dual D) g := by
    rw [layerEnergy_eq_mean_pairing _ _ _ _ _ _ hdualnormal, hdualmean]
    rfl
  rw [← henergy]
  exact layerEnergy_minimum_of_flux_match (dual_posDef hA) (dual_posDef hB)
    n a g z hdualnormal

end HierarchicalLaminates.TwoWell
