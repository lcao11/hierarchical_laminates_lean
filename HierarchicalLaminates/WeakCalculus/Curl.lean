module

public import HierarchicalLaminates.WeakCalculus.Parseval

/-! Rotated periodic weak gradients are equilibrated and have zero mean. -/

@[expose] public section
noncomputable section

namespace HierarchicalLaminates.WeakCalculus

open MeasureTheory HierarchicalLaminates.Periodic

def curlLinear : PhysicalGradient →ₗ[ℝ] PhysicalGradient where
  toFun v := WithLp.toLp 2 (fun c => if c.1 = 0 then -v (1, c.2) else v (0, c.2))
  map_add' := by
    intro v w
    ext c
    rcases c with ⟨i, a⟩
    fin_cases i <;> simp [add_comm]
  map_smul' := by
    intro r v
    ext c
    rcases c with ⟨i, a⟩
    fin_cases i <;> simp

def curlOperator : PhysicalGradient →L[ℝ] PhysicalGradient :=
  curlLinear.toContinuousLinearMap

def curlField : PhysicalField →L[ℝ] PhysicalField :=
  curlOperator.compLpL 2 domainMeasure

theorem curlOperator_apply_zero (v : PhysicalGradient) (a : Fin 16) :
    curlOperator v (0, a) = -v (1, a) := by
  simp [curlOperator, curlLinear]

theorem curlOperator_apply_one (v : PhysicalGradient) (a : Fin 16) :
    curlOperator v (1, a) = v (0, a) := by
  simp [curlOperator, curlLinear]

theorem curlField_component_zero (v : PhysicalField) (a : Fin 16) :
    componentField 0 a (curlField v) = -componentField 1 a v := by
  apply Lp.ext
  filter_upwards [curlOperator.coeFn_compLpL v,
    (EuclideanSpace.proj (𝕜 := ℝ) (0, a)).coeFn_compLpL (curlField v),
    (EuclideanSpace.proj (𝕜 := ℝ) (1, a)).coeFn_compLpL v,
    Lp.coeFn_neg (componentField 1 a v)] with q hc h0 h1 hn
  change _ = _ at hn
  simp only [Pi.neg_apply] at hn
  change _ = _ at h0 h1
  erw [h0, hn, h1, hc]
  exact curlOperator_apply_zero _ _

theorem curlField_component_one (v : PhysicalField) (a : Fin 16) :
    componentField 1 a (curlField v) = componentField 0 a v := by
  apply Lp.ext
  filter_upwards [curlOperator.coeFn_compLpL v,
    (EuclideanSpace.proj (𝕜 := ℝ) (1, a)).coeFn_compLpL (curlField v),
    (EuclideanSpace.proj (𝕜 := ℝ) (0, a)).coeFn_compLpL v] with q hc h1 h0
  erw [h1, h0, hc]
  exact curlOperator_apply_one _ _

theorem physical_inner_components (v w : PhysicalField) :
    inner ℝ v w = ∑ a : Fin 16, ∑ i : Fin 2,
      inner ℝ (componentField i a v) (componentField i a w) := by
  simp_rw [L2.inner_def]
  trans ∫ q, ∑ a : Fin 16, ∑ i : Fin 2,
    inner ℝ (componentField i a v q) (componentField i a w q) ∂domainMeasure
  swap
  · rw [integral_finsetSum Finset.univ (fun a _ =>
      integrable_finsetSum _ (fun i _ => L2.integrable_inner
        (componentField i a v) (componentField i a w)))]
    apply Finset.sum_congr rfl
    intro a _
    exact integral_finsetSum Finset.univ (fun i _ => L2.integrable_inner
      (componentField i a v) (componentField i a w))
  apply integral_congr_ae
  have hv : ∀ᵐ q ∂domainMeasure, ∀ i a,
      componentField i a v q = v q (i, a) := by
    simp only [Filter.eventually_all]
    intro i a
    exact (EuclideanSpace.proj (𝕜 := ℝ) (i, a)).coeFn_compLpL v
  have hw : ∀ᵐ q ∂domainMeasure, ∀ i a,
      componentField i a w q = w q (i, a) := by
    simp only [Filter.eventually_all]
    intro i a
    exact (EuclideanSpace.proj (𝕜 := ℝ) (i, a)).coeFn_compLpL w
  filter_upwards [hv, hw] with q hvq hwq
  simp only [hvq, hwq, PiLp.inner_apply, Real.inner_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem weakCurl_weakGradient_zero {u v : Fin 16 → ScalarField}
    {du dv : PhysicalField} (hu : HasWeakGradient u du) (hv : HasWeakGradient v dv) :
    inner ℝ (curlField du) dv = 0 := by
  rw [physical_inner_components]
  apply Finset.sum_eq_zero
  intro a _
  rw [Fin.sum_univ_two, curlField_component_zero, curlField_component_one,
    inner_neg_left]
  have h := mixed_pairing (u := u a) (v := v a)
    (hu 0 a) (hu 1 a) (hv 0 a) (hv 1 a)
  linarith

theorem weakCurl_gradient_zero {u : Fin 16 → ScalarField} {du : PhysicalField}
    (hu : HasWeakGradient u du) (g : PhysicalField) (hg : g ∈ gradientSpace) :
    inner ℝ (curlField du) g = 0 := by
  let L := innerSL ℝ (curlField du)
  have hweak : weakGradientSpace ≤ L.ker := by
    rintro w ⟨v, hv⟩
    exact weakCurl_weakGradient_zero hu hv
  exact weakGradientSpace.topologicalClosure_minimal hweak L.isClosed_ker hg

theorem weakCurl_mean_zero {u : Fin 16 → ScalarField} {du : PhysicalField}
    (hu : HasWeakGradient u du) : meanField (curlField du) = 0 := by
  rw [show curlField du = curlOperator.compLpL 2 domainMeasure du from rfl,
    meanField_comp, hu.mean_zero, map_zero]

end HierarchicalLaminates.WeakCalculus
