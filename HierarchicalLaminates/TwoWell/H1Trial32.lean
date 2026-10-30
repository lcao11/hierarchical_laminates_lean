module

public import HierarchicalLaminates.TwoWell.H1Trial
public import HierarchicalLaminates.TwoWell.Sobolev32

/-! Quasiconvex trial estimates for every periodic 32-potential H¹ variation. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.TwoWell

open MeasureTheory HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Lamination
  HierarchicalLaminates.GClosure

theorem quasiconvex_h1_trial_inequality32 (F : Gradient32) (u v : SobolevPotential) :
    quasiconvexEnvelope32 twoWellEnergy32 F ≤
      ∫ q, twoWellEnergy32 (weakTrial32 F u v q) ∂domainMeasure := by
  rw [quasiconvexEnvelope32_transport]
  simpa only [twoWellEnergy32_join32,weakTrial32] using
    quasiconvex_h1_trial_inequality (split32 F) u v

def leftWeak32 (u : WeakPotential (Fin 32)) : SobolevPotential :=
  (u.restrict (fun a => componentSumEquiv (.inl a))).toSixteen

def rightWeak32 (u : WeakPotential (Fin 32)) : SobolevPotential :=
  (u.restrict (fun a => componentSumEquiv (.inr a))).toSixteen

/-- Splitting a weak potential preserves every gradient component. -/
theorem weakTrial32_components (F : Gradient32) (u : WeakPotential (Fin 32)) :
    weakTrial (split32 F) (leftWeak32 u) (rightWeak32 u) =ᵐ[domainMeasure]
      fun q => split32 (fun c => F c+u.gradient c q) := by
  filter_upwards [assembleComponents_coe
      ((u.restrict (fun a => componentSumEquiv (.inl a))).gradient),
    assembleComponents_coe
      ((u.restrict (fun a => componentSumEquiv (.inr a))).gradient)] with q hl hr
  apply Prod.ext
  · ext ⟨i,a⟩
    change (split32 F).1 (i,a)+
      assembleComponents (u.restrict (fun a => componentSumEquiv (.inl a))).gradient q (i,a) = _
    rw [hl,split32_left_apply,split32_left_apply]
    rfl
  · ext ⟨i,a⟩
    change (split32 F).2 (i,a)+
      assembleComponents (u.restrict (fun a => componentSumEquiv (.inr a))).gradient q (i,a) = _
    rw [hr,split32_right_apply,split32_right_apply]
    rfl

/-- The C¹-defined envelope satisfies the trial inequality for every H¹ potential. -/
theorem quasiconvex_h1_trial_inequality32_weak (F : Gradient32)
    (u : WeakPotential (Fin 32)) :
    quasiconvexEnvelope32 twoWellEnergy32 F ≤
      ∫ q, twoWellEnergy32 (fun c => F c+u.gradient c q) ∂domainMeasure := by
  have h := quasiconvex_h1_trial_inequality32 F (leftWeak32 u) (rightWeak32 u)
  have heq :
      (∫ q, twoWellEnergy32 (weakTrial32 F (leftWeak32 u) (rightWeak32 u) q)
        ∂domainMeasure) =
      ∫ q, twoWellEnergy32 (fun c => F c+u.gradient c q) ∂domainMeasure := by
    apply integral_congr_ae
    filter_upwards [weakTrial32_components F u] with q hq
    simp only [weakTrial32,twoWellEnergy32_join32]
    rw [hq,twoWellEnergy32_eq]
  exact heq ▸ h

end HierarchicalLaminates.TwoWell
