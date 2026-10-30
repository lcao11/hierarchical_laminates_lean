module
public import HierarchicalLaminates.GClosure.Interfaces
/-!
# Uniform positivity and symmetry in the tensor closure
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace HierarchicalLaminates.GClosure
open Matrix HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material HierarchicalLaminates.Lamination
  HierarchicalLaminates.Analysis HierarchicalLaminates.Homogenization
theorem quadraticEnergy_continuous (F : Gradient (Fin 16)) :
    Continuous (fun B : Tensor (Fin 16) => quadraticEnergy B F) := by
  unfold quadraticEnergy dotProduct Matrix.mulVec
  fun_prop
theorem GClosure_isHermitian {θ : ℝ} {B : Tensor (Fin 16)} (hB : B ∈ GClosure θ) :
    B.IsHermitian := by
  have hc : IsClosed {C : Tensor (Fin 16) | C.IsHermitian} := by
    simp only [Matrix.IsHermitian.ext_iff, star_trivial, Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (by fun_prop) (by fun_prop)
  apply closure_minimal (t := {C : Tensor (Fin 16) | C.IsHermitian}) ?_ hc hB
  rintro C ⟨b, _, _, rfl⟩
  exact effectiveMatrix_isHermitian b
theorem GClosure_coercive {θ : ℝ} {B : Tensor (Fin 16)} (hB : B ∈ GClosure θ)
    (F : PhysicalGradient) : (1/4 : ℝ)*‖F‖*‖F‖ ≤ quadraticEnergy B (F : Fin 2 × Fin 16 → ℝ) := by
  have hc : IsClosed {C : Tensor (Fin 16) | ∀ F : PhysicalGradient,
      (1/4 : ℝ)*‖F‖*‖F‖ ≤ quadraticEnergy C (F : Fin 2 × Fin 16 → ℝ)} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun F => isClosed_le continuous_const (quadraticEnergy_continuous _)
  have hs : periodicBinaryTensors θ ⊆ {C : Tensor (Fin 16) | ∀ F : PhysicalGradient,
      (1/4 : ℝ)*‖F‖*‖F‖ ≤ quadraticEnergy C (F : Fin 2 × Fin 16 → ℝ)} := by
    rintro C ⟨b, _, _, rfl⟩ F
    have h := periodicEffective_coercive (coefficientLaw b) (1/4) (by norm_num)
      (coefficientLaw_coercive b) F
    change (1/4 : ℝ)*‖F‖*‖F‖ ≤ inner ℝ (HierarchicalLaminates.Material.effectiveOperator b F) F at h
    rw [← effectiveMatrix_operator b, real_inner_comm] at h
    simpa only [Matrix.inner_toEuclideanCLM, star_trivial, quadraticEnergy] using h
  exact closure_minimal hs hc hB F
theorem GClosure_posDef {θ : ℝ} {B : Tensor (Fin 16)} (hB : B ∈ GClosure θ) : B.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (GClosure_isHermitian hB)
  intro v hv
  let F : PhysicalGradient := WithLp.toLp 2 v
  have hF : F ≠ 0 := by
    intro hz
    apply hv
    exact congrArg (fun f : PhysicalGradient => (f : Fin 2 × Fin 16 → ℝ)) hz
  have hp : 0 < (1/4 : ℝ)*‖F‖*‖F‖ := by positivity
  exact lt_of_lt_of_le hp (GClosure_coercive hB F)
end HierarchicalLaminates.GClosure
