module

public import HierarchicalLaminates.Lamination.LayerFormula
public import Mathlib.Tactic.FinCases

/-!
# Spatial block tensors with the spatial index first
-/

@[expose] public section

namespace HierarchicalLaminates.Lamination

open Matrix

noncomputable section

variable {m : Type*} [Fintype m] [DecidableEq m]

def spatialBlocks (A D : Matrix m m ℝ) : Tensor m :=
  Matrix.of fun i j => if i.1 = j.1 then
    (if i.1 = 0 then A else D) i.2 j.2 else 0

omit [DecidableEq m] in
theorem spatialBlocks_energy (A D : Matrix m m ℝ) (F : Gradient m) :
    quadraticEnergy (spatialBlocks A D) F =
      quadraticFormValue A (fun a => F (0, a)) +
        quadraticFormValue D (fun a => F (1, a)) := by
  simp [quadraticEnergy, quadraticFormValue, spatialBlocks, Matrix.mulVec,
    dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem normalMatrix_spatialBlocks (A D : Matrix m m ℝ) (n : LayerNormal) :
    (normalMatrix n)ᵀ * spatialBlocks A D * normalMatrix n =
      (n.coordinates 0 ^ 2) • A + (n.coordinates 1 ^ 2) • D := by
  ext a b
  simp [Matrix.mul_apply, normalMatrix, spatialBlocks, Matrix.transpose_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, Pi.single_apply]
  ring

end

end HierarchicalLaminates.Lamination
