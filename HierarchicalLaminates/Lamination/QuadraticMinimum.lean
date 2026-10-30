module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Attained minima of strictly positive quadratic functions

Finite-dimensional quadratic minimization gives the minimizer and energy
for the compatible-jump definition of lamination.
-/

@[expose] public section

namespace HierarchicalLaminates.Lamination

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

def quadraticFormValue (M : Matrix n n ℝ) (z : n → ℝ) : ℝ := z ⬝ᵥ M *ᵥ z

/-- Equality at every loading determines a real self-adjoint tensor. -/
theorem hermitian_eq_of_quadratic_eq {A B : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hquadratic : ∀ z : n → ℝ, quadraticFormValue A z = quadraticFormValue B z) :
    A = B := by
  ext i j
  have hi := hquadratic (Pi.single i 1)
  have hj := hquadratic (Pi.single j 1)
  have hij := hquadratic (Pi.single i 1 + Pi.single j 1)
  have hsymA := hA.apply i j
  have hsymB := hB.apply i j
  simp only [star_trivial] at hsymA hsymB
  simp [quadraticFormValue, Matrix.mulVec] at hi hj hij
  linarith

omit [DecidableEq n] in
theorem quadratic_add_smul {C : Matrix n n ℝ} (hC : C.IsHermitian)
    (F G : n → ℝ) (a : ℝ) :
    quadraticFormValue C (F + a • G) = quadraticFormValue C F +
      2 * a * (G ⬝ᵥ C *ᵥ F) + a ^ 2 * quadraticFormValue C G := by
  have hcross : F ⬝ᵥ C *ᵥ G = G ⬝ᵥ C *ᵥ F := by
    simpa only [star_trivial] using hC.star_dotProduct_mulVec_comm F G
  simp only [quadraticFormValue, Matrix.mulVec_add, Matrix.mulVec_smul,
    add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [hcross]
  ring

omit [DecidableEq n] in
theorem quadratic_sandwich {p : Type*} [Fintype p]
    (C : Matrix n n ℝ) (J : Matrix n p ℝ) (z : p → ℝ) :
    quadraticFormValue (Jᵀ * C * J) z = quadraticFormValue C (J *ᵥ z) := by
  unfold quadraticFormValue
  simp only [← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

omit [DecidableEq n] in
theorem quadratic_sub_smul (A B : Matrix n n ℝ) (a : ℝ) (F : n → ℝ) :
    quadraticFormValue (A - a • B) F =
      quadraticFormValue A F - a * quadraticFormValue B F := by
  simp only [quadraticFormValue, Matrix.sub_mulVec, Matrix.smul_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul]

theorem complete_square {M : Matrix n n ℝ} (hM : M.PosDef)
    (b z : n → ℝ) :
    quadraticFormValue M z - 2 * (z ⬝ᵥ b) =
      quadraticFormValue M (z - M⁻¹ *ᵥ b) - b ⬝ᵥ M⁻¹ *ᵥ b := by
  let _ := hM.isUnit.invertible
  let v := M⁻¹ *ᵥ b
  have hMv : M *ᵥ v = b := by
    simp [v, Matrix.mulVec_mulVec]
  have hcross : v ⬝ᵥ M *ᵥ z = z ⬝ᵥ b := by
    have h := hM.isHermitian.star_dotProduct_mulVec_comm v z
    simpa only [star_trivial, hMv] using h
  have hvb : v ⬝ᵥ b = b ⬝ᵥ v := dotProduct_comm _ _
  change quadraticFormValue M z - 2 * (z ⬝ᵥ b) =
    quadraticFormValue M (z - v) - b ⬝ᵥ v
  simp only [quadraticFormValue, Matrix.mulVec_sub, sub_dotProduct,
    dotProduct_sub, hMv, hcross, hvb]
  ring

/-- The quadratic minimum is attained at the inverse applied to the source. -/
theorem quadratic_minimum {M : Matrix n n ℝ} (hM : M.PosDef) (b : n → ℝ) :
    IsLeast (Set.range fun z : n → ℝ =>
      quadraticFormValue M z - 2 * (z ⬝ᵥ b)) (-(b ⬝ᵥ M⁻¹ *ᵥ b)) := by
  refine ⟨?_, ?_⟩
  · refine ⟨M⁻¹ *ᵥ b, ?_⟩
    dsimp only
    rw [complete_square hM]
    simp [quadraticFormValue]
  · rintro value ⟨z, rfl⟩
    dsimp only
    rw [complete_square hM]
    have hnon := hM.posSemidef.dotProduct_mulVec_nonneg (z - M⁻¹ *ᵥ b)
    simp only [star_trivial] at hnon
    dsimp [quadraticFormValue]
    linarith

end

end HierarchicalLaminates.Lamination
