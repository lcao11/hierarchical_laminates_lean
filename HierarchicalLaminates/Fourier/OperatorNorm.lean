module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic.Linarith

/-!
# Euclidean operator norms from positive matrix bounds

The Rayleigh quotient bounds the real Euclidean operator norm.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Fourier

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem euclidean_norm_le_of_psd_bound {A : Matrix n n ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hA : A.PosSemidef)
    (hupper : (c • (1 : Matrix n n ℝ) - A).PosSemidef) :
    ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A‖ ≤ c := by
  let T : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n :=
    Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A
  have hsym : T.IsSymmetric := by
    change (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A :
      EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n).IsSymmetric
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hA.isHermitian
  rw [show Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A = T from rfl,
    T.norm_eq_iSup_rayleighQuotient hsym]
  apply ciSup_le
  intro v
  have hnonneg : 0 ≤ inner ℝ v (T v) := by
    simpa only [T, Matrix.inner_toEuclideanCLM, star_trivial] using
      hA.dotProduct_mulVec_nonneg (v : n → ℝ)
  have hbound : inner ℝ v (T v) ≤ c * ‖v‖ ^ 2 := by
    have hu : 0 ≤ inner ℝ v (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)
        (c • (1 : Matrix n n ℝ) - A) v) := by
      simpa only [Matrix.inner_toEuclideanCLM, star_trivial] using
        hupper.dotProduct_mulVec_nonneg (v : n → ℝ)
    simp only [map_sub, map_smul, map_one, sub_apply, smul_apply, one_apply_eq_self,
      inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq] at hu
    simpa only [T] using sub_nonneg.mp hu
  by_cases hv : v = 0
  · simpa [hv] using hc
  have hvpos : 0 < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.mpr hv) _
  change |RCLike.re (inner ℝ (T v) v) / ‖v‖ ^ 2| ≤ c
  rw [RCLike.re_to_real, real_inner_comm, abs_of_nonneg (div_nonneg hnonneg (sq_nonneg _)),
    div_le_iff₀ hvpos]
  exact hbound

theorem euclidean_apply_norm_le_of_psd_bound {A : Matrix n n ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hA : A.PosSemidef)
    (hupper : (c • (1 : Matrix n n ℝ) - A).PosSemidef)
    (v : EuclideanSpace ℝ n) :
    ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A v‖ ≤ c * ‖v‖ := by
  exact (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A).le_opNorm v |>.trans
    (mul_le_mul_of_nonneg_right (euclidean_norm_le_of_psd_bound hc hA hupper)
      (norm_nonneg v))

end HierarchicalLaminates.Fourier
