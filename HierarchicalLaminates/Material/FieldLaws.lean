module

public import HierarchicalLaminates.Periodic.FieldSpace
public import HierarchicalLaminates.Analysis.CellProblem
public import Mathlib.Tactic.Linarith

/-!
# Pointwise constitutive bounds for periodic L² operators
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Material

open MeasureTheory
open HierarchicalLaminates.Periodic HierarchicalLaminates.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem fieldLaw_symmetric (A : Periodic.Field E →L[ℝ] Periodic.Field E)
    (a : Domain → E →L[ℝ] E)
    (hrep : ∀ f : Periodic.Field E, A f =ᵐ[domainMeasure] fun q => a q (f q))
    (hsym : ∀ q v w, inner ℝ (a q v) w = inner ℝ v (a q w)) :
    SymmetricLaw A := by
  intro f g
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hrep f, hrep g] with q hf hg
  rw [hf, hg]
  exact hsym q (f q) (g q)

theorem fieldLaw_norm_bound (A : Periodic.Field E →L[ℝ] Periodic.Field E)
    (a : Domain → E →L[ℝ] E)
    (hrep : ∀ f : Periodic.Field E, A f =ᵐ[domainMeasure] fun q => a q (f q))
    (M : ℝ) (hbound : ∀ q v, ‖a q v‖ ≤ M * ‖v‖) (f : Periodic.Field E) :
    ‖A f‖ ≤ M * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hrep f] with q hq
  rw [hq]
  exact hbound q (f q)

theorem fieldLaw_coercive (A : Periodic.Field E →L[ℝ] Periodic.Field E)
    (a : Domain → E →L[ℝ] E)
    (hrep : ∀ f : Periodic.Field E, A f =ᵐ[domainMeasure] fun q => a q (f q))
    (mu : ℝ) (hlower : ∀ q v, mu * inner ℝ v v ≤ inner ℝ (a q v) v) :
    CoerciveLaw A mu := by
  intro f
  have hff : Integrable (fun q => inner ℝ (f q) (f q)) domainMeasure :=
    MeasureTheory.L2.integrable_inner f f
  have haf : Integrable (fun q => inner ℝ ((A f) q) (f q)) domainMeasure :=
    MeasureTheory.L2.integrable_inner (A f) f
  have hle : ∫ q, mu * inner ℝ (f q) (f q) ∂domainMeasure ≤
      ∫ q, inner ℝ ((A f) q) (f q) ∂domainMeasure := by
    apply integral_mono_ae (hff.const_mul mu) haf
    filter_upwards [hrep f] with q hq
    rw [hq]
    exact hlower q (f q)
  rw [integral_const_mul] at hle
  have hinner : mu * inner ℝ f f ≤ inner ℝ (A f) f := by
    simpa only [MeasureTheory.L2.inner_def] using hle
  simpa only [real_inner_self_eq_norm_sq, pow_two, mul_assoc] using hinner

end HierarchicalLaminates.Material
