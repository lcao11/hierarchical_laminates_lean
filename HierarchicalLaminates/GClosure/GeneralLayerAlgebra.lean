module

public import HierarchicalLaminates.GClosure.Interfaces

/-! Optimal layer jumps and the associated macroscopic fields and fluxes. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open Matrix HierarchicalLaminates HierarchicalLaminates.Lamination

variable {m : Type*} [Fintype m] [DecidableEq m]

def optimalLayerJump (B C : Tensor m) (n : LayerNormal) (a : ℝ)
    (F : Gradient m) : m → ℝ :=
  (jumpStiffness B C n a)⁻¹ *ᵥ (jumpSourceMatrix B C n *ᵥ F)

theorem optimalLayerJump_equation {B C : Tensor m} (hB : B.PosDef) (hC : C.PosDef)
    (n : LayerNormal) {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (F : Gradient m) :
    jumpStiffness B C n a *ᵥ optimalLayerJump B C n a F =
      jumpSourceMatrix B C n *ᵥ F := by
  let := (jumpStiffness_posDef hB hC n ha₀ ha₁).isUnit.invertible
  simp [optimalLayerJump, Matrix.mulVec_mulVec]

def firstOptimalField (B C : Tensor m) (n : LayerNormal) (a : ℝ)
    (F : Gradient m) : Gradient m :=
  firstLayerField n a F (optimalLayerJump B C n a F)

def secondOptimalField (B C : Tensor m) (n : LayerNormal) (a : ℝ)
    (F : Gradient m) : Gradient m :=
  secondLayerField n a F (optimalLayerJump B C n a F)

theorem optimal_fields_mean (B C : Tensor m) (n : LayerNormal) (a : ℝ)
    (F : Gradient m) :
    a • firstOptimalField B C n a F + (1-a) • secondOptimalField B C n a F = F :=
  layer_fields_mean n a F _

theorem normal_action_source (B C : Tensor m) (n : LayerNormal) (F : Gradient m) :
    (normalMatrix n)ᵀ *ᵥ (C *ᵥ F - B *ᵥ F) = jumpSourceMatrix B C n *ᵥ F := by
  rw [jumpSourceMatrix, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec]

theorem normal_action_stiffness (B C : Tensor m) (n : LayerNormal) (a : ℝ)
    (z : m → ℝ) :
    (normalMatrix n)ᵀ *ᵥ
      ((1-a) • (B *ᵥ normalJump n z) + a • (C *ᵥ normalJump n z)) =
      jumpStiffness B C n a *ᵥ z := by
  rw [jumpStiffness, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    normalMatrix_mulVec, matrixAverage, Matrix.add_mulVec,
    Matrix.smul_mulVec, Matrix.smul_mulVec]
  congr 1
  simp only [sub_sub_cancel]

theorem optimal_normal_flux_match {B C : Tensor m} (hB : B.PosDef) (hC : C.PosDef)
    (n : LayerNormal) {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (F : Gradient m) :
    (normalMatrix n)ᵀ *ᵥ (B *ᵥ firstOptimalField B C n a F) =
      (normalMatrix n)ᵀ *ᵥ (C *ᵥ secondOptimalField B C n a F) := by
  have heq :
      B *ᵥ firstOptimalField B C n a F - C *ᵥ secondOptimalField B C n a F =
      -(C *ᵥ F - B *ᵥ F) +
      ((1-a) • (B *ᵥ normalJump n (optimalLayerJump B C n a F)) +
        a • (C *ᵥ normalJump n (optimalLayerJump B C n a F))) := by
    simp only [firstOptimalField, secondOptimalField, firstLayerField, secondLayerField,
      Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul]
    module
  apply sub_eq_zero.mp
  rw [← Matrix.mulVec_sub, heq, Matrix.mulVec_add, Matrix.mulVec_neg,
    normal_action_source, normal_action_stiffness, optimalLayerJump_equation hB hC n ha₀ ha₁,
    neg_add_cancel]

theorem source_transpose {B C : Tensor m} (hB : B.IsHermitian) (hC : C.IsHermitian)
    (n : LayerNormal) :
    (jumpSourceMatrix B C n)ᵀ = (C-B) * normalMatrix n := by
  rw [jumpSourceMatrix, Matrix.transpose_mul, Matrix.transpose_transpose]
  congr 1
  exact (hC.sub hB).eq

theorem optimal_flux_mean {B C : Tensor m} (hB : B.IsHermitian) (hC : C.IsHermitian)
    (n : LayerNormal) (a : ℝ) (F : Gradient m) :
    a • (B *ᵥ firstOptimalField B C n a F) +
      (1-a) • (C *ᵥ secondOptimalField B C n a F) =
      computedLayerTensor B C n a *ᵥ F := by
  rw [computedLayerTensor, Matrix.sub_mulVec, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, source_transpose hB hC,
    ← Matrix.mulVec_mulVec, normalMatrix_mulVec]
  change a • (B *ᵥ firstLayerField n a F (optimalLayerJump B C n a F)) +
      (1-a) • (C *ᵥ secondLayerField n a F (optimalLayerJump B C n a F)) =
      matrixAverage a B C *ᵥ F - (a*(1-a)) •
        ((C-B) *ᵥ normalJump n (optimalLayerJump B C n a F))
  simp only [firstLayerField, secondLayerField, matrixAverage, Matrix.mulVec_add,
    Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.sub_mulVec]
  module

end HierarchicalLaminates.GClosure
