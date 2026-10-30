module

public import HierarchicalLaminates.GClosure.GeneralLayerAlgebra
public import Mathlib.Topology.Instances.Matrix

/-!
# Continuity of the layer formula in its tensors, proportion and direction
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open Filter Matrix HierarchicalLaminates HierarchicalLaminates.Lamination
open scoped Topology

instance layerNormalTopology : TopologicalSpace LayerNormal :=
  TopologicalSpace.induced LayerNormal.coordinates inferInstance

theorem normalCoordinates_continuous : Continuous LayerNormal.coordinates :=
  continuous_induced_dom

theorem normalMatrix_continuous {m : Type*} [Fintype m] [DecidableEq m] :
    Continuous (normalMatrix (m := m)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases h : j = i.2
  · subst j
    simpa [normalMatrix, Function.comp_def] using
      (continuous_apply i.1).comp normalCoordinates_continuous
  · simp only [normalMatrix, Matrix.of_apply, Pi.single_eq_of_ne h]
    exact continuous_const

theorem matrix_mul_tendsto {α p q s : Type*} [Fintype q]
    {l : Filter α} {A : α → Matrix p q ℝ} {B : α → Matrix q s ℝ}
    {A₀ : Matrix p q ℝ} {B₀ : Matrix q s ℝ}
    (hA : Tendsto A l (nhds A₀)) (hB : Tendsto B l (nhds B₀)) :
    Tendsto (fun x => A x * B x) l (nhds (A₀ * B₀)) := by
  have hc : Continuous (fun x : Matrix p q ℝ × Matrix q s ℝ => x.1 * x.2) :=
    continuous_fst.matrix_mul continuous_snd
  exact hc.continuousAt.tendsto.comp (hA.prodMk_nhds hB)

theorem matrix_transpose_tendsto {α p q : Type*} {l : Filter α}
    {A : α → Matrix p q ℝ} {A₀ : Matrix p q ℝ}
    (hA : Tendsto A l (nhds A₀)) :
    Tendsto (fun x => (A x)ᵀ) l (nhds A₀ᵀ) :=
  (continuous_id.matrix_transpose.continuousAt.tendsto).comp hA

theorem matrixAverage_tendsto {α m : Type*} [Fintype m] {l : Filter α}
    {B C : α → Tensor m} {a : α → ℝ} {B₀ C₀ : Tensor m} {a₀ : ℝ}
    (hB : Tendsto B l (nhds B₀)) (hC : Tendsto C l (nhds C₀))
    (ha : Tendsto a l (nhds a₀)) :
    Tendsto (fun x => matrixAverage (a x) (B x) (C x)) l
      (nhds (matrixAverage a₀ B₀ C₀)) := by
  exact (ha.smul hB).add ((tendsto_const_nhds.sub ha).smul hC)

theorem computedLayerTensor_tendsto {α m : Type*} [Fintype m] [DecidableEq m]
    {l : Filter α} {B C : α → Tensor m} {n : α → LayerNormal} {a : α → ℝ}
    {B₀ C₀ : Tensor m} {n₀ : LayerNormal} {a₀ : ℝ}
    (hB : Tendsto B l (nhds B₀)) (hC : Tendsto C l (nhds C₀))
    (hn : Tendsto n l (nhds n₀)) (ha : Tendsto a l (nhds a₀))
    (hBpos : B₀.PosDef) (hCpos : C₀.PosDef) (ha₀ : 0 ≤ a₀) (ha₁ : a₀ ≤ 1) :
    Tendsto (fun x => computedLayerTensor (B x) (C x) (n x) (a x)) l
      (nhds (computedLayerTensor B₀ C₀ n₀ a₀)) := by
  have hN : Tendsto (fun x => normalMatrix (m := m) (n x)) l (nhds (normalMatrix n₀)) :=
    normalMatrix_continuous.continuousAt.tendsto.comp hn
  have hNt := matrix_transpose_tendsto hN
  have hsource : Tendsto (fun x => jumpSourceMatrix (B x) (C x) (n x)) l
      (nhds (jumpSourceMatrix B₀ C₀ n₀)) :=
    matrix_mul_tendsto hNt (hC.sub hB)
  have hstiff : Tendsto (fun x => jumpStiffness (B x) (C x) (n x) (a x)) l
      (nhds (jumpStiffness B₀ C₀ n₀ a₀)) :=
    matrix_mul_tendsto (matrix_mul_tendsto hNt
      (matrixAverage_tendsto hB hC (tendsto_const_nhds.sub ha))) hN
  have hM := jumpStiffness_posDef hBpos hCpos n₀ ha₀ ha₁
  have hdet : (jumpStiffness B₀ C₀ n₀ a₀).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det _).mp hM.isUnit)
  have hinv : ContinuousAt (Inv.inv : Matrix m m ℝ → Matrix m m ℝ)
      (jumpStiffness B₀ C₀ n₀ a₀) := by
    apply continuousAt_matrix_inv
    simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hdet)
  have hMinv := hinv.tendsto.comp hstiff
  exact (matrixAverage_tendsto hB hC ha).sub
    ((ha.mul (tendsto_const_nhds.sub ha)).smul
      (matrix_mul_tendsto (matrix_mul_tendsto (matrix_transpose_tendsto hsource) hMinv) hsource))

end HierarchicalLaminates.GClosure
