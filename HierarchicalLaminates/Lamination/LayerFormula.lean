module

public import HierarchicalLaminates.Lamination.LayerEnergy
public import HierarchicalLaminates.Lamination.HarmonicBounds

/-!
# The minimum of the layer jump energy

Minimization over all compatible jumps gives a Schur-complement formula for
the variational layer tensor defined in `LayerEnergy`.
-/

@[expose] public section

namespace HierarchicalLaminates.Lamination

open Matrix

noncomputable section

variable {m : Type*} [Fintype m] [DecidableEq m]

def normalMatrix (n : LayerNormal) : Matrix (Fin 2 × m) m ℝ :=
  Matrix.of fun i => Pi.single i.2 (n.coordinates i.1)

@[simp]
theorem normalMatrix_mulVec (n : LayerNormal) (z : m → ℝ) :
    normalMatrix n *ᵥ z = normalJump n z := by
  ext i
  simp [normalMatrix, Matrix.mulVec, normalJump]

def jumpStiffness (C₁ C₂ : Tensor m) (n : LayerNormal) (weight : ℝ) : Matrix m m ℝ :=
  (normalMatrix n)ᵀ * matrixAverage (1 - weight) C₁ C₂ * normalMatrix n

def jumpSourceMatrix (C₁ C₂ : Tensor m) (n : LayerNormal) :
    Matrix m (Fin 2 × m) ℝ :=
  (normalMatrix n)ᵀ * (C₂ - C₁)

def computedLayerTensor (C₁ C₂ : Tensor m) (n : LayerNormal) (weight : ℝ) : Tensor m :=
  matrixAverage weight C₁ C₂ - (weight * (1 - weight)) •
    ((jumpSourceMatrix C₁ C₂ n)ᵀ * (jumpStiffness C₁ C₂ n weight)⁻¹ *
      jumpSourceMatrix C₁ C₂ n)

omit [DecidableEq m] in
theorem quadratic_average (A B : Tensor m) (weight : ℝ) (F : Gradient m) :
    quadraticFormValue (matrixAverage weight A B) F =
      weight * quadraticFormValue A F + (1 - weight) * quadraticFormValue B F := by
  simp only [quadraticFormValue, matrixAverage, Matrix.add_mulVec,
    Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]

omit [Fintype m] [DecidableEq m] in
theorem average_isHermitian {C₁ C₂ : Tensor m}
    (h₁ : C₁.IsHermitian) (h₂ : C₂.IsHermitian) (weight : ℝ) :
    (matrixAverage weight C₁ C₂).IsHermitian :=
  (h₁.smul (IsSelfAdjoint.all weight)).add (h₂.smul (IsSelfAdjoint.all (1 - weight)))

theorem jumpStiffness_posDef {C₁ C₂ : Tensor m} (h₁ : C₁.PosDef) (h₂ : C₂.PosDef)
    (n : LayerNormal) {weight : ℝ} (hweight₀ : 0 ≤ weight) (hweight₁ : weight ≤ 1) :
    (jumpStiffness C₁ C₂ n weight).PosDef := by
  have hW := average_posDef (sub_nonneg.mpr hweight₁) (by linarith : 1 - weight ≤ 1) h₁ h₂
  have hJ : Function.Injective (normalMatrix n : Matrix (Fin 2 × m) m ℝ).mulVec := by
    intro z w hzw
    apply normalJump_injective n
    simpa only [normalMatrix_mulVec] using hzw
  simpa only [jumpStiffness, Matrix.conjTranspose_eq_transpose_of_trivial] using
    hW.conjTranspose_mul_mul_same hJ

theorem layer_energy_expansion {C₁ C₂ : Tensor m}
    (h₁ : C₁.IsHermitian) (h₂ : C₂.IsHermitian)
    (n : LayerNormal) (weight : ℝ) (F : Gradient m) (z : m → ℝ) :
    layerEnergy C₁ C₂ n weight F z =
      quadraticFormValue (matrixAverage weight C₁ C₂) F + weight * (1 - weight) *
        (quadraticFormValue (jumpStiffness C₁ C₂ n weight) z -
          2 * (z ⬝ᵥ jumpSourceMatrix C₁ C₂ n *ᵥ F)) := by
  let G := normalJump n z
  have hfirst : quadraticEnergy C₁ (firstLayerField n weight F z) =
      quadraticFormValue C₁ F + 2 * (1 - weight) * (G ⬝ᵥ C₁ *ᵥ F) +
        (1 - weight) ^ 2 * quadraticFormValue C₁ G :=
    quadratic_add_smul h₁ F G (1 - weight)
  have hsecond : quadraticEnergy C₂ (secondLayerField n weight F z) =
      quadraticFormValue C₂ F + 2 * (-weight) * (G ⬝ᵥ C₂ *ᵥ F) +
        (-weight) ^ 2 * quadraticFormValue C₂ G := by
    change quadraticFormValue C₂ (F - weight • G) = _
    rw [sub_eq_add_neg, ← neg_smul]
    exact quadratic_add_smul h₂ F G (-weight)
  have hstiff : quadraticFormValue (jumpStiffness C₁ C₂ n weight) z =
      (1 - weight) * quadraticFormValue C₁ G + weight * quadraticFormValue C₂ G := by
    rw [jumpStiffness, quadratic_sandwich, normalMatrix_mulVec, quadratic_average]
    ring
  have hsource : z ⬝ᵥ jumpSourceMatrix C₁ C₂ n *ᵥ F =
      G ⬝ᵥ C₂ *ᵥ F - G ⬝ᵥ C₁ *ᵥ F := by
    unfold jumpSourceMatrix
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec,
      dotProduct_comm, normalMatrix_mulVec]
    simp only [Matrix.sub_mulVec, dotProduct_sub]
    rfl
  rw [layerEnergy, hfirst, hsecond, hstiff, hsource, quadratic_average]
  ring

theorem computedLayerTensor_energy (C₁ C₂ : Tensor m) (n : LayerNormal) (weight : ℝ)
    (F : Gradient m) :
    quadraticEnergy (computedLayerTensor C₁ C₂ n weight) F =
      quadraticFormValue (matrixAverage weight C₁ C₂) F - weight * (1 - weight) *
        quadraticFormValue (jumpStiffness C₁ C₂ n weight)⁻¹
          (jumpSourceMatrix C₁ C₂ n *ᵥ F) := by
  change quadraticFormValue (computedLayerTensor C₁ C₂ n weight) F = _
  rw [computedLayerTensor, quadratic_sub_smul, quadratic_sandwich]

/-- The Schur complement represents the attained minimum at every loading,
for every real unit normal and proportion, including endpoint proportions. -/
theorem computedLayerTensor_represents_minimum {C₁ C₂ : Tensor m}
    (h₁ : C₁.PosDef) (h₂ : C₂.PosDef) (n : LayerNormal) (weight : LayerProportion) :
    IsLayerTensor C₁ C₂ n weight (computedLayerTensor C₁ C₂ n weight) := by
  have hM := jumpStiffness_posDef h₁ h₂ n weight.property.1 weight.property.2
  have hhermitian : (computedLayerTensor C₁ C₂ n (weight : ℝ)).IsHermitian := by
    have hsandwich := Matrix.isHermitian_conjTranspose_mul_mul
      (jumpSourceMatrix C₁ C₂ n) hM.inv.isHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hsandwich
    exact (average_isHermitian h₁.isHermitian h₂.isHermitian (weight : ℝ)).sub
      (hsandwich.smul (IsSelfAdjoint.all _))
  refine ⟨hhermitian, fun F => ?_⟩
  let b := jumpSourceMatrix C₁ C₂ n *ᵥ F
  let v := (jumpStiffness C₁ C₂ n (weight : ℝ))⁻¹ *ᵥ b
  have hexpansion (z : m → ℝ) :
      layerEnergy C₁ C₂ n (weight : ℝ) F z =
        quadraticFormValue (matrixAverage (weight : ℝ) C₁ C₂) F +
          (weight : ℝ) * (1 - (weight : ℝ)) *
            (quadraticFormValue (jumpStiffness C₁ C₂ n (weight : ℝ)) (z - v) -
              b ⬝ᵥ (jumpStiffness C₁ C₂ n (weight : ℝ))⁻¹ *ᵥ b) := by
    rw [layer_energy_expansion h₁.isHermitian h₂.isHermitian, complete_square hM]
  have hweight : 0 ≤ (weight : ℝ) * (1 - (weight : ℝ)) :=
    mul_nonneg weight.property.1 (sub_nonneg.mpr weight.property.2)
  refine ⟨?_, ?_⟩
  · refine ⟨v, ?_⟩
    rw [hexpansion, computedLayerTensor_energy]
    simp only [sub_self, quadraticFormValue, Matrix.mulVec_zero, dotProduct_zero]
    dsimp [b]
    ring
  · rintro value ⟨z, rfl⟩
    rw [hexpansion, computedLayerTensor_energy]
    have hnon := hM.posSemidef.dotProduct_mulVec_nonneg (z - v)
    simp only [star_trivial] at hnon
    have hproduct := mul_nonneg hweight hnon
    dsimp [quadraticFormValue, b] at *
    nlinarith

end

end HierarchicalLaminates.Lamination
