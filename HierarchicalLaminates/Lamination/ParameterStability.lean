module

public import HierarchicalLaminates.Lamination.HarmonicBounds
public import HierarchicalLaminates.Lamination.HarmonicFormula
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Convert

/-!
# Algebraic stability of the laminate parameter

For a linear matrix space closed under inversion of positive-definite
members, the laminate formula preserves the parameter space. Harmonic-mean
order bounds preserve the parameter interval when the shifted matrices are
positive definite.
-/

@[expose] public section

namespace HierarchicalLaminates.Lamination

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

def PositiveInverseClosed (S : Submodule ℝ (Matrix n n ℝ)) : Prop :=
  ∀ {A}, A ∈ S → A.PosDef → A⁻¹ ∈ S

def laminateParameter (Λ H₁ H₂ : Matrix n n ℝ) (weight : ℝ) : Matrix n n ℝ :=
  Λ - harmonicMean weight (Λ - H₁) (Λ - H₂)

theorem laminateParameter_correction (Λ H₁ H₂ : Matrix n n ℝ)
    (h₁ : (Λ - H₁).PosDef) (h₂ : (Λ - H₂).PosDef)
    {weight : ℝ} (hweight₀ : 0 ≤ weight) (hweight₁ : weight ≤ 1) :
    laminateParameter Λ H₁ H₂ weight = matrixAverage weight H₁ H₂ +
      (weight * (1 - weight)) • ((H₁ - H₂) *
        (Λ - matrixAverage (1 - weight) H₁ H₂)⁻¹ * (H₁ - H₂)) := by
  have hmean (w : ℝ) : matrixAverage w (Λ - H₁) (Λ - H₂) =
      Λ - matrixAverage w H₁ H₂ := by
    dsimp [matrixAverage]
    module
  have hdelta : (Λ - H₁) - (Λ - H₂) = -(H₁ - H₂) := by abel
  rw [laminateParameter, harmonicMean_correction h₁ h₂ hweight₀ hweight₁,
    hmean weight, hmean (1 - weight), hdelta]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  abel

/-- Harmonic averaging preserves the parameter space and its entire order
interval, at every proportion in the closed unit interval. -/
theorem laminateParameter_stable {S : Submodule ℝ (Matrix n n ℝ)}
    (hinverse : PositiveInverseClosed S)
    {Λ H₁ H₂ : Matrix n n ℝ} {ρ weight : ℝ}
    (hΛmem : Λ ∈ S) (hH₁mem : H₁ ∈ S) (hH₂mem : H₂ ∈ S)
    (hΛ : Λ.PosDef) (hbase : (Λ - ρ • (1 : Matrix n n ℝ)).PosDef)
    (hH₁lower : H₁.PosSemidef) (hH₂lower : H₂.PosSemidef)
    (hH₁upper : (ρ • (1 : Matrix n n ℝ) - H₁).PosSemidef)
    (hH₂upper : (ρ • (1 : Matrix n n ℝ) - H₂).PosSemidef)
    (hweight₀ : 0 ≤ weight) (hweight₁ : weight ≤ 1) :
    laminateParameter Λ H₁ H₂ weight ∈ S ∧
    (laminateParameter Λ H₁ H₂ weight).PosSemidef ∧
    (ρ • (1 : Matrix n n ℝ) - laminateParameter Λ H₁ H₂ weight).PosSemidef := by
  have hK₁ : (Λ - H₁).PosDef := by
    have h := hbase.add_posSemidef hH₁upper
    convert h using 1; abel
  have hK₂ : (Λ - H₂).PosDef := by
    have h := hbase.add_posSemidef hH₂upper
    convert h using 1; abel
  have hL₁ : (Λ - H₁ - (Λ - ρ • (1 : Matrix n n ℝ))).PosSemidef := by
    convert hH₁upper using 1; abel
  have hL₂ : (Λ - H₂ - (Λ - ρ • (1 : Matrix n n ℝ))).PosSemidef := by
    convert hH₂upper using 1; abel
  have hU₁ : (Λ - (Λ - H₁)).PosSemidef := by
    convert hH₁lower using 1; abel
  have hU₂ : (Λ - (Λ - H₂)).PosSemidef := by
    convert hH₂lower using 1; abel
  obtain ⟨_, hlower, hupper⟩ :=
    harmonicMean_bounds hweight₀ hweight₁ hK₁ hK₂ hbase hΛ hL₁ hL₂ hU₁ hU₂
  have haverageMem : matrixAverage weight (Λ - H₁)⁻¹ (Λ - H₂)⁻¹ ∈ S :=
    S.add_mem (S.smul_mem weight (hinverse (S.sub_mem hΛmem hH₁mem) hK₁))
      (S.smul_mem (1 - weight) (hinverse (S.sub_mem hΛmem hH₂mem) hK₂))
  have haveragePos : (matrixAverage weight (Λ - H₁)⁻¹ (Λ - H₂)⁻¹).PosDef :=
    average_posDef hweight₀ hweight₁ hK₁.inv hK₂.inv
  refine ⟨S.sub_mem hΛmem (hinverse haverageMem haveragePos), hupper, ?_⟩
  change (ρ • (1 : Matrix n n ℝ) -
    (Λ - harmonicMean weight (Λ - H₁) (Λ - H₂))).PosSemidef
  convert hlower using 1; abel

end

end HierarchicalLaminates.Lamination
