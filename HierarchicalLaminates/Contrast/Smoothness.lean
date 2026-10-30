module

public import HierarchicalLaminates.Contrast.CellIdentification
public import HierarchicalLaminates.Contrast.Regularity
public import HierarchicalLaminates.Corrector.Smoothness

/-!
# Joint spatial smoothness of the response and correctors

For each fixed `0 < r < 2 / 3`, summable polynomial Fourier moments give joint
`C∞` regularity of the real lifts on `ℝ²`. This includes all mixed spatial
derivatives of the response, potential, full gradient and associated source
fields.

`sourceComponent_physical` identifies the synthesized source with its
pointwise expression in the physical total field.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.Contrast

open Matrix Fourier Corrector Periodic
open scoped ContDiff

theorem solution_moments {r : ℝ} (hr : 0 < r) (hrlt : r < 2/3) :
    HasFrequencyMoments (solution r) := solution_frequency_moment_summable hr hrlt

theorem response_smooth {r : ℝ} (hr : 0 < r) (hrlt : r < 2/3) :
    ContDiff ℝ ∞ (torusLift (response r)) :=
  cosineSynthesis_smooth (solution r) (solution_moments hr hrlt)

theorem potential_smooth {r : ℝ} (hr : 0 < r) (hrlt : r < 2/3)
    (w : ReducedSpace) (a : Fin 16) :
    ContDiff ℝ ∞ (realLift (potential (solution r) w a)) :=
  potential_smooth_of_moments (solution r) (solution_moments hr hrlt) w a

theorem potentialVector_smooth {r : ℝ} (hr : 0 < r) (hrlt : r < 2/3) (w : ReducedSpace) :
    ContDiff ℝ ∞ (fun x : LiftDomain => WithLp.toLp 2
      (fun a : Fin 16 => potential (solution r) w a (fun i => (x i : UnitAddCircle)))) :=
  potentialVector_smooth_of_moments (solution r) (solution_moments hr hrlt) w

theorem gradient_smooth {r : ℝ} (hr : 0 < r) (hrlt : r < 2/3) (w : ReducedSpace) :
    ContDiff ℝ ∞ (torusLift (gradientContinuous (solution r) w)) :=
  gradientContinuous_smooth_of_moments (solution r) (solution_moments hr hrlt) w

theorem total_smooth {r : ℝ} (hr : 0 < r) (hrlt : r < 2/3) (z : PotentialVector) :
    ContDiff ℝ ∞ (torusLift (totalContinuous r z)) := by
  change ContDiff ℝ ∞ (fun x => horizontalLoading z+
    torusLift (gradientContinuous (solution r) (reducedLoading z)) x)
  exact contDiff_const.add (gradient_smooth hr hrlt (reducedLoading z))

def multiplierResponse (r : ℝ) : C(PeriodicDomain,ReducedOperator) :=
  cosineSynthesis (reducedFourierMultiplier (solution r))

theorem multiplierResponse_smooth {r : ℝ} (hr : 0 < r) (hrlt : r < 2/3) :
    ContDiff ℝ ∞ (torusLift (multiplierResponse r)) :=
  cosineSynthesis_smooth _ (reducedFourierMultiplier_moments (solution_moments hr hrlt))

def sourceComponent (r : ℝ) (z : PotentialVector) (a : Fin 16) : C(PeriodicDomain,ℝ) :=
  ContinuousMap.const PeriodicDomain ((factorR *ᵥ (reducedLoading z : Fin 8 → ℝ)) a) +
    cosineSynthesis (amplitudeCoefficients (reducedFourierMultiplier (solution r)) (reducedLoading z) a)

theorem sourceComponent_physical (r : ℝ) (z : PotentialVector) (a : Fin 16) (q : PeriodicDomain) :
    sourceComponent r z a q =
      (factorR *ᵥ (factorRᵀ *ᵥ (fun b => totalContinuous r z q (0,b)))) a := by
  rw [sourceComponent,ContinuousMap.add_apply,ContinuousMap.const_apply,
    amplitude_synthesis,amplitudeOperator_apply]
  have hred := reduced_gradient_synthesis (solution r) (reducedLoading z) q
  have hrow : (fun b => totalContinuous r z q (0,b)) =
      (z : Fin 16 → ℝ)+(fun b => gradientContinuous (solution r) (reducedLoading z) q (0,b)) := by
    ext b
    simp [totalContinuous,horizontalLoading]
  rw [hrow,Matrix.mulVec_add,Matrix.mulVec_add,hred]
  rfl

theorem sourceComponent_smooth {r : ℝ} (hr : 0 < r) (hrlt : r < 2/3)
    (z : PotentialVector) (a : Fin 16) :
    ContDiff ℝ ∞ (realLift (sourceComponent r z a)) := by
  have hs := cosineSynthesis_smooth
    (amplitudeCoefficients (reducedFourierMultiplier (solution r)) (reducedLoading z) a)
    (amplitudeCoefficients_moments (reducedFourierMultiplier_moments (solution_moments hr hrlt))
      (reducedLoading z) a)
  exact contDiff_const.add hs

end HierarchicalLaminates.Contrast
