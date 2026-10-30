module

public import HierarchicalLaminates.Corrector.Multipliers
public import HierarchicalLaminates.Fourier.IntegrationByParts

/-!
# A real periodic H¹ potential

Sine synthesis and its derivatives give the potential and its weak Sobolev
gradient.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Corrector

open HierarchicalLaminates.Fourier HierarchicalLaminates.Periodic

set_option maxHeartbeats 0 in
def gradientContinuous (f : ReducedCoefficients) (w : ReducedSpace) :
    C(PeriodicDomain, PhysicalGradient) where
  toFun q := WithLp.toLp 2 (fun j => gradientComponent f w j.1 j.2 q)
  continuous_toFun := by
    exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 × Fin 16 => ℝ)).comp
      (continuous_pi (fun j : Fin 2 × Fin 16 =>
        (HierarchicalLaminates.Corrector.gradientComponent f w j.1 j.2).continuous))

@[simp]
lemma gradientContinuous_apply (f : ReducedCoefficients) (w : ReducedSpace)
    (q : PeriodicDomain) (i : Fin 2) (a : Fin 16) :
    gradientContinuous f w q (i, a) = gradientComponent f w i a q := rfl

def sobolevPotential (f : ReducedCoefficients) (w : ReducedSpace) : SobolevPotential where
  potential a := continuousField (potential f w a)
  gradient := continuousField (gradientContinuous f w)
  weakGradient := continuous_hasWeakGradient _ _ (fun i a q t =>
    potential_hasDerivAt f w i a q t)

lemma physical_gradient_admissible (f : ReducedCoefficients) (w : ReducedSpace) :
    continuousField (gradientContinuous f w) ∈ gradientSpace :=
  weakGradient_mem_gradientSpace (sobolevPotential f w)

lemma physical_gradient_mean_zero (f : ReducedCoefficients) (w : ReducedSpace) :
    meanField (continuousField (gradientContinuous f w)) = 0 :=
  (sobolevPotential f w).weakGradient.mean_zero

/-- The physical corrector reconstructed from the infinite Neumann response. -/
def smoothCorrector (w : ReducedSpace) : SobolevPotential := sobolevPotential rhoSolution w

end HierarchicalLaminates.Corrector
