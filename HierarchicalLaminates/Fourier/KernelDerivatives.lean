module

public import HierarchicalLaminates.Fourier.Characters
public import HierarchicalLaminates.Periodic.WeakGradient
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.FunProp

/-!
# Smooth periodic cosine and sine tests

Coordinate-flow derivatives provide the smooth tests in the weak-gradient
interface. Integer frequencies on the unit torus give the factor `2 * pi * k_i`.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Fourier

open scoped ContDiff

theorem phaseCharacter_domain_add (k : ℤ × ℤ) (x y : PeriodicDomain) :
    phaseCharacter k (x + y) = phaseCharacter k x * phaseCharacter k y := by
  simp only [phaseCharacter, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    Pi.add_apply, fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul,
    Finset.prod_mul_distrib]

theorem phaseCharacter_single (k : ℤ × ℤ) (i : Fin 2) (s : UnitAddCircle) :
    phaseCharacter k (Pi.single i s) = fourier (frequencyVector k i) s := by
  simp only [phaseCharacter, UnitAddTorus.mFourier, ContinuousMap.coe_mk]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

theorem phaseCharacter_flow (k : ℤ × ℤ) (i : Fin 2) (q : PeriodicDomain) (s : ℝ) :
    phaseCharacter k (HierarchicalLaminates.Periodic.coordinateFlow i q s) =
      phaseCharacter k q * fourier (frequencyVector k i) (s : UnitAddCircle) := by
  rw [HierarchicalLaminates.Periodic.coordinateFlow, phaseCharacter_domain_add, phaseCharacter_single]

theorem phaseCharacter_lift (k : ℤ × ℤ) (q : Fin 2 → ℝ) :
    phaseCharacter k (fun i => (q i : UnitAddCircle)) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((k.1 : ℂ) * (q 0 : ℂ) + (k.2 : ℂ) * (q 1 : ℂ))) := by
  simp only [phaseCharacter, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    frequencyVector, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, mul_one, fourier_coe_apply]
  rw [← Complex.exp_add]
  congr 1
  norm_num
  ring

theorem cosineKernel_smooth (k : ℤ × ℤ) :
    ContDiff ℝ ∞ (HierarchicalLaminates.Periodic.realLift (cosineKernel k)) := by
  have heq : HierarchicalLaminates.Periodic.realLift (cosineKernel k) =
      fun q : Fin 2 → ℝ =>
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          ((k.1 : ℂ) * (q 0 : ℂ) + (k.2 : ℂ) * (q 1 : ℂ)))).re := by
    ext q
    exact congrArg Complex.re (phaseCharacter_lift k q)
  rw [heq]
  apply ContDiff.continuousLinearMap_comp Complex.reCLM
  have hq (i : Fin 2) : ContDiff ℝ ∞ (fun q : Fin 2 → ℝ => (q i : ℂ)) :=
    (contDiff_apply ℝ (fun _ : Fin 2 => ℝ) i).continuousLinearMap_comp Complex.ofRealCLM
  fun_prop (disch := aesop)

theorem sineKernel_smooth (k : ℤ × ℤ) :
    ContDiff ℝ ∞ (HierarchicalLaminates.Periodic.realLift (sineKernel k)) := by
  have heq : HierarchicalLaminates.Periodic.realLift (sineKernel k) =
      fun q : Fin 2 → ℝ =>
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          ((k.1 : ℂ) * (q 0 : ℂ) + (k.2 : ℂ) * (q 1 : ℂ)))).im := by
    ext q
    exact congrArg Complex.im (phaseCharacter_lift k q)
  rw [heq]
  apply ContDiff.continuousLinearMap_comp Complex.imCLM
  have hq (i : Fin 2) : ContDiff ℝ ∞ (fun q : Fin 2 → ℝ => (q i : ℂ)) :=
    (contDiff_apply ℝ (fun _ : Fin 2 => ℝ) i).continuousLinearMap_comp Complex.ofRealCLM
  fun_prop (disch := aesop)

theorem hasDerivAt_phaseCharacter_flow (k : ℤ × ℤ) (i : Fin 2) (q : PeriodicDomain) :
    HasDerivAt (fun s : ℝ => phaseCharacter k (HierarchicalLaminates.Periodic.coordinateFlow i q s))
      (2 * (Real.pi : ℂ) * Complex.I * (frequencyVector k i : ℂ) * phaseCharacter k q) 0 := by
  convert (hasDerivAt_fourier (1 : ℝ) (frequencyVector k i) 0).const_mul (phaseCharacter k q) using 1
  · ext s
    exact phaseCharacter_flow k i q s
  · norm_num
    ring

theorem hasDerivAt_cosineKernel_flow (k : ℤ × ℤ) (i : Fin 2) (q : PeriodicDomain) :
    HasDerivAt (fun s : ℝ => cosineKernel k (HierarchicalLaminates.Periodic.coordinateFlow i q s))
      (-(2 * Real.pi * (frequencyVector k i : ℝ)) * sineKernel k q) 0 := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_phaseCharacter_flow k i q)
  convert h using 1
  · rfl
  · simp [sineKernel, Complex.mul_re, Complex.mul_im]

theorem hasDerivAt_sineKernel_flow (k : ℤ × ℤ) (i : Fin 2) (q : PeriodicDomain) :
    HasDerivAt (fun s : ℝ => sineKernel k (HierarchicalLaminates.Periodic.coordinateFlow i q s))
      (2 * Real.pi * (frequencyVector k i : ℝ) * cosineKernel k q) 0 := by
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_phaseCharacter_flow k i q)
  convert h using 1
  · rfl
  · simp [cosineKernel, Complex.mul_re, Complex.mul_im]

theorem hasDerivAt_phaseCharacter_flow_at (k : ℤ × ℤ) (i : Fin 2)
    (q : PeriodicDomain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => phaseCharacter k (HierarchicalLaminates.Periodic.coordinateFlow i q s))
      (2 * (Real.pi : ℂ) * Complex.I * (frequencyVector k i : ℂ) *
        phaseCharacter k (HierarchicalLaminates.Periodic.coordinateFlow i q t)) t := by
  convert (hasDerivAt_fourier (1 : ℝ) (frequencyVector k i) t).const_mul
    (phaseCharacter k q) using 1
  · ext s
    exact phaseCharacter_flow k i q s
  · rw [phaseCharacter_flow]
    norm_num
    ring

theorem hasDerivAt_cosineKernel_flow_at (k : ℤ × ℤ) (i : Fin 2)
    (q : PeriodicDomain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => cosineKernel k (HierarchicalLaminates.Periodic.coordinateFlow i q s))
      (-(2 * Real.pi * (frequencyVector k i : ℝ)) *
        sineKernel k (HierarchicalLaminates.Periodic.coordinateFlow i q t)) t := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_phaseCharacter_flow_at k i q t)
  convert h using 1
  · rfl
  · simp [sineKernel, Complex.mul_re, Complex.mul_im]

theorem hasDerivAt_sineKernel_flow_at (k : ℤ × ℤ) (i : Fin 2)
    (q : PeriodicDomain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => sineKernel k (HierarchicalLaminates.Periodic.coordinateFlow i q s))
      (2 * Real.pi * (frequencyVector k i : ℝ) *
        cosineKernel k (HierarchicalLaminates.Periodic.coordinateFlow i q t)) t := by
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_phaseCharacter_flow_at k i q t)
  convert h using 1
  · rfl
  · simp [cosineKernel, Complex.mul_re, Complex.mul_im]

def cosineTest (k : ℤ × ℤ) : HierarchicalLaminates.Periodic.SmoothTest where
  value := cosineKernel k
  derivative i := (-(2 * Real.pi * (frequencyVector k i : ℝ))) • sineKernel k
  smooth := cosineKernel_smooth k
  hasPartial i q := hasDerivAt_cosineKernel_flow k i q

def sineTest (k : ℤ × ℤ) : HierarchicalLaminates.Periodic.SmoothTest where
  value := sineKernel k
  derivative i := (2 * Real.pi * (frequencyVector k i : ℝ)) • cosineKernel k
  smooth := sineKernel_smooth k
  hasPartial i q := hasDerivAt_sineKernel_flow k i q

end HierarchicalLaminates.Fourier
