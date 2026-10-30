module

public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Energy values on a set and its closure

For a continuous energy, every lower bound on an admissible set extends to its
closure. A minimum attained on that closure is therefore the greatest lower
bound of the energy values on the admissible set.
-/

@[expose] public section

namespace HierarchicalLaminates.Analysis

variable {X : Type*} [TopologicalSpace X]

/-- Every continuous energy lower bound on a set extends to its closure. -/
theorem energy_lower_bound_on_closure (Q : X → ℝ) (hQ : Continuous Q)
    (S : Set X) (c : ℝ) (hc : ∀ x ∈ S, c ≤ Q x) :
    ∀ x ∈ closure S, c ≤ Q x := by
  have hclosed : IsClosed {x : X | c ≤ Q x} := isClosed_le continuous_const hQ
  exact closure_minimal (fun x hx => hc x hx) hclosed

/-- A minimum attained on the closure is the greatest lower bound on the set. -/
theorem energy_isGLB_of_min_on_closure (Q : X → ℝ) (hQ : Continuous Q)
    (S : Set X) (x : X) (hx : x ∈ closure S)
    (hmin : ∀ y ∈ closure S, Q x ≤ Q y) : IsGLB (Q '' S) (Q x) := by
  constructor
  · rintro y ⟨z, hz, rfl⟩
    exact hmin z (subset_closure hz)
  · intro c hc
    exact energy_lower_bound_on_closure Q hQ S c (fun y hy => hc ⟨y, hy, rfl⟩) x hx

/-- Closing an admissible class changes no continuous minimum energy value. -/
theorem energy_sInf_eq_of_min_on_closure (Q : X → ℝ) (hQ : Continuous Q)
    (S : Set X) (hS : S.Nonempty) (x : X) (hx : x ∈ closure S)
    (hmin : ∀ y ∈ closure S, Q x ≤ Q y) : sInf (Q '' S) = Q x :=
  (energy_isGLB_of_min_on_closure Q hQ S x hx hmin).csInf_eq (hS.image Q)

end HierarchicalLaminates.Analysis
