module

public import HierarchicalLaminates.Corrector.Potential

/-!
# Physical flux coefficients and their exact equilibrium identity
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Corrector

open HierarchicalLaminates.Fourier HierarchicalLaminates.Periodic

abbrev PhysicalIndex := Fin 2 × Fin 16

def coordinateInjection (j : PhysicalIndex) : ℝ →L[ℝ] PhysicalGradient :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : PhysicalIndex => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℝ (fun _ : PhysicalIndex => ℝ) j)

@[simp]
lemma coordinateInjection_apply (j l : PhysicalIndex) (c : ℝ) :
    coordinateInjection j c l = if l = j then c else 0 := by
  simp [coordinateInjection]

def assembleCoefficients (f : PhysicalIndex → Coefficients HierarchicalLaminates.Frequency ℝ) :
    Coefficients HierarchicalLaminates.Frequency PhysicalGradient :=
  ∑ j : PhysicalIndex, multiplierCLM (fun _ => coordinateInjection j) ‖coordinateInjection j‖
    (fun _ v => (coordinateInjection j).le_opNorm v) (f j)

@[simp]
lemma assembleCoefficients_apply
    (f : PhysicalIndex → Coefficients HierarchicalLaminates.Frequency ℝ) (k) (j : PhysicalIndex) :
    assembleCoefficients f k j = f j k := by
  simp only [assembleCoefficients, lp.coeFn_sum, Finset.sum_apply, multiplierCLM_apply]
  change (∑ x : PhysicalIndex, coordinateInjection x (f x k)) j = _
  simp

def gradientVectorCoefficients (f : ReducedCoefficients) (w : ReducedSpace) :
    Coefficients HierarchicalLaminates.Frequency PhysicalGradient :=
  assembleCoefficients fun j => gradientCoefficients f w j.1 j.2

def fluxComponentCoefficients (f : ReducedCoefficients) (w : ReducedSpace)
    (i : Fin 2) (a : Fin 16) : Coefficients HierarchicalLaminates.Frequency ℝ :=
  if i = 0 then gradientCoefficients f w 0 a - amplitudeCoefficients f w a
  else HierarchicalLaminates.verticalDiagonalR a • gradientCoefficients f w 1 a

def fluxCoefficients (f : ReducedCoefficients) (w : ReducedSpace) :
    Coefficients HierarchicalLaminates.Frequency PhysicalGradient :=
  assembleCoefficients fun j => fluxComponentCoefficients f w j.1 j.2

lemma fluxCoefficients_divergence (f : ReducedCoefficients) (w : ReducedSpace)
    (k : HierarchicalLaminates.Frequency) (a : Fin 16) :
    ∑ i : Fin 2, angularFrequency k i * fluxCoefficients f w k (i, a) = 0 := by
  have href := reference_divergence_identity k a
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, fluxCoefficients,
    assembleCoefficients_apply, fluxComponentCoefficients, Fin.succ_ne_zero, ↓reduceIte,
    lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    gradientCoefficients, scalarMultiplier_apply, angularFrequency,
    frequencyVector, Matrix.cons_val_zero, Matrix.cons_val_succ]
  have hh := congrArg (fun x : ℝ => 2 * Real.pi * x * amplitudeCoefficients f w a k) href
  nlinarith [hh]

end HierarchicalLaminates.Corrector
