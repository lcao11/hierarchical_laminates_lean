module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# Real cosine and sine kernels on the unit torus

Real and imaginary parts of scalar characters give the trigonometric
identities for real-valued Fourier synthesis.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Fourier

abbrev PeriodicDomain := UnitAddTorus (Fin 2)

def frequencyVector (k : ℤ × ℤ) : Fin 2 → ℤ := ![k.1, k.2]

theorem frequencyVector_add (k l : ℤ × ℤ) :
    frequencyVector (k + l) = frequencyVector k + frequencyVector l := by
  ext i
  fin_cases i <;> rfl

theorem frequencyVector_neg (k : ℤ × ℤ) :
    frequencyVector (-k) = -frequencyVector k := by
  ext i
  fin_cases i <;> rfl

def phaseCharacter (k : ℤ × ℤ) : C(PeriodicDomain, ℂ) :=
  UnitAddTorus.mFourier (frequencyVector k)

theorem phaseCharacter_zero (x : PeriodicDomain) : phaseCharacter (0, 0) x = 1 := by
  simp [phaseCharacter, frequencyVector, UnitAddTorus.mFourier, Fin.prod_univ_succ]

theorem phaseCharacter_add (k l : ℤ × ℤ) (x : PeriodicDomain) :
    phaseCharacter (k + l) x = phaseCharacter k x * phaseCharacter l x := by
  unfold phaseCharacter
  rw [frequencyVector_add]
  exact UnitAddTorus.mFourier_add

theorem phaseCharacter_neg (k : ℤ × ℤ) (x : PeriodicDomain) :
    phaseCharacter (-k) x = starRingEnd ℂ (phaseCharacter k x) := by
  unfold phaseCharacter
  rw [frequencyVector_neg]
  exact UnitAddTorus.mFourier_neg

theorem phaseCharacter_norm_le (k : ℤ × ℤ) (x : PeriodicDomain) :
    ‖phaseCharacter k x‖ ≤ 1 := by
  calc
    ‖phaseCharacter k x‖ ≤ ‖phaseCharacter k‖ := (phaseCharacter k).norm_coe_le_norm x
    _ = 1 := UnitAddTorus.mFourier_norm (n := frequencyVector k)

def cosineKernel (k : ℤ × ℤ) : C(PeriodicDomain, ℝ) :=
  ⟨fun x => (phaseCharacter k x).re, Complex.continuous_re.comp (phaseCharacter k).continuous⟩

def sineKernel (k : ℤ × ℤ) : C(PeriodicDomain, ℝ) :=
  ⟨fun x => (phaseCharacter k x).im, Complex.continuous_im.comp (phaseCharacter k).continuous⟩

theorem cosineKernel_zero : cosineKernel (0, 0) = 1 := by
  ext x
  simp [cosineKernel, phaseCharacter_zero]

theorem sineKernel_zero : sineKernel (0, 0) = 0 := by
  ext x
  simp [sineKernel, phaseCharacter_zero]

theorem cosineKernel_norm_le (k : ℤ × ℤ) : ‖cosineKernel k‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ zero_le_one).2
  intro x
  exact (Complex.abs_re_le_norm (phaseCharacter k x)).trans (phaseCharacter_norm_le k x)

theorem sineKernel_norm_le (k : ℤ × ℤ) : ‖sineKernel k‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ zero_le_one).2
  intro x
  exact (Complex.abs_im_le_norm (phaseCharacter k x)).trans (phaseCharacter_norm_le k x)

theorem cosineKernel_abs_le (k : ℤ × ℤ) (x : PeriodicDomain) :
    |cosineKernel k x| ≤ 1 :=
  ((cosineKernel k).norm_coe_le_norm x).trans (cosineKernel_norm_le k)

theorem sineKernel_abs_le (k : ℤ × ℤ) (x : PeriodicDomain) :
    |sineKernel k x| ≤ 1 :=
  ((sineKernel k).norm_coe_le_norm x).trans (sineKernel_norm_le k)

theorem cosineKernel_neg (k : ℤ × ℤ) : cosineKernel (-k) = cosineKernel k := by
  ext x
  simp [cosineKernel, phaseCharacter_neg]

theorem sineKernel_neg (k : ℤ × ℤ) : sineKernel (-k) = -sineKernel k := by
  ext x
  simp [sineKernel, phaseCharacter_neg]

theorem cosineKernel_add (k l : ℤ × ℤ) (x : PeriodicDomain) :
    cosineKernel (k + l) x =
      cosineKernel k x * cosineKernel l x - sineKernel k x * sineKernel l x := by
  change (phaseCharacter (k + l) x).re = _
  rw [phaseCharacter_add]
  exact Complex.mul_re _ _

theorem sineKernel_add (k l : ℤ × ℤ) (x : PeriodicDomain) :
    sineKernel (k + l) x =
      cosineKernel k x * sineKernel l x + sineKernel k x * cosineKernel l x := by
  change (phaseCharacter (k + l) x).im = _
  rw [phaseCharacter_add]
  exact Complex.mul_im _ _

theorem cosineKernel_add_pair (k l : ℤ × ℤ) (x : PeriodicDomain) :
    cosineKernel (k + l) x + cosineKernel (k - l) x =
      2 * cosineKernel k x * cosineKernel l x := by
  rw [sub_eq_add_neg, cosineKernel_add, cosineKernel_add, cosineKernel_neg, sineKernel_neg]
  simp only [ContinuousMap.neg_apply]
  ring

end HierarchicalLaminates.Fourier
