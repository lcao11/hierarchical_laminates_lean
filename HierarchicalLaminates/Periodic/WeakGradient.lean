module

public import HierarchicalLaminates.Periodic.FieldSpace
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.Tactic.Ring

/-!
# Periodic weak gradients

Tests are smooth real functions on the torus, with coordinate derivatives
along real translation curves. A weak gradient satisfies the integration-by-parts
identity against every such test. The potential components and all gradient
components are square-integrable.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Periodic

open MeasureTheory
open scoped ContDiff

def coordinateFlow (i : Fin 2) (q : Domain) (s : ℝ) : Domain :=
  q + Pi.single i (s : UnitAddCircle)

def realLift (f : C(Domain, ℝ)) (x : Fin 2 → ℝ) : ℝ :=
  f (fun i => (x i : UnitAddCircle))

/-- An ordinary smooth periodic test with its coordinate derivatives. -/
structure SmoothTest where
  value : C(Domain, ℝ)
  derivative : Fin 2 → C(Domain, ℝ)
  smooth : ContDiff ℝ ∞ (realLift value)
  hasPartial : ∀ i q,
    HasDerivAt (fun s : ℝ => value (coordinateFlow i q s)) (derivative i q) 0

def constantTest (c : ℝ) : SmoothTest where
  value := ContinuousMap.const Domain c
  derivative := fun _ => ContinuousMap.const Domain 0
  smooth := contDiff_const
  hasPartial := fun _ _ => hasDerivAt_const _ _

def componentField (i : Fin 2) (a : Fin 16) : PhysicalField →L[ℝ] ScalarField :=
  (EuclideanSpace.proj (𝕜 := ℝ) (i, a)).compLpL 2 domainMeasure

/-- The distributional derivative identity on the periodic cell. -/
def HasWeakGradient (u : Fin 16 → ScalarField) (g : PhysicalField) : Prop :=
  ∀ i a (test : SmoothTest),
    inner ℝ (componentField i a g) (continuousField test.value) =
      -inner ℝ (u a) (continuousField (test.derivative i))

/-- A vector-valued periodic H¹ potential with its weak-gradient witness. -/
structure SobolevPotential where
  potential : Fin 16 → ScalarField
  gradient : PhysicalField
  weakGradient : HasWeakGradient potential gradient

theorem weakGradient_zero : HasWeakGradient (fun _ => 0) 0 := by
  intro i a test
  simp [componentField]

theorem HasWeakGradient.add {u v : Fin 16 → ScalarField} {g h : PhysicalField}
    (hu : HasWeakGradient u g) (hv : HasWeakGradient v h) :
    HasWeakGradient (fun a => u a + v a) (g + h) := by
  intro i a test
  simp only [map_add, inner_add_left]
  rw [hu, hv]
  ring

theorem HasWeakGradient.smul {u : Fin 16 → ScalarField} {g : PhysicalField}
    (hu : HasWeakGradient u g) (c : ℝ) :
    HasWeakGradient (fun a => c • u a) (c • g) := by
  intro i a test
  simp only [map_smul, real_inner_smul_left]
  rw [hu]
  ring

/-- The range of periodic weak Sobolev gradients. -/
def weakGradientSpace : Submodule ℝ PhysicalField where
  carrier := {g | ∃ u : Fin 16 → ScalarField, HasWeakGradient u g}
  zero_mem' := ⟨fun _ => 0, weakGradient_zero⟩
  add_mem' := by
    rintro g h ⟨u, hu⟩ ⟨v, hv⟩
    exact ⟨fun a => u a + v a, hu.add hv⟩
  smul_mem' := by
    rintro c g ⟨u, hu⟩
    exact ⟨fun a => c • u a, hu.smul c⟩

theorem mem_weakGradientSpace_iff (g : PhysicalField) :
    g ∈ weakGradientSpace ↔ ∃ u : Fin 16 → ScalarField, HasWeakGradient u g := Iff.rfl

def gradientSpace : Submodule ℝ PhysicalField := weakGradientSpace.topologicalClosure

theorem weakGradient_mem_gradientSpace (u : SobolevPotential) :
    u.gradient ∈ gradientSpace := by
  apply weakGradientSpace.le_topologicalClosure
  exact ⟨u.potential, u.weakGradient⟩

theorem HasWeakGradient.component_mean_zero {u : Fin 16 → ScalarField} {g : PhysicalField}
    (hu : HasWeakGradient u g) (i : Fin 2) (a : Fin 16) :
    meanField (componentField i a g) = 0 := by
  have h := hu i a (constantTest 1)
  simp only [constantTest, continuousField_const, map_zero, inner_zero_right, neg_zero] at h
  have hp := constant_mean_pairing (1 : ℝ) (componentField i a g)
  rw [real_inner_comm] at h
  simpa only [Real.inner_apply, one_mul] using hp.symm.trans h

theorem component_mean_eq_coordinate (g : PhysicalField) (i : Fin 2) (a : Fin 16) :
    meanField (componentField i a g) = meanField g (i, a) := by
  exact meanField_comp (EuclideanSpace.proj (𝕜 := ℝ) (i, a)) g

theorem HasWeakGradient.mean_zero {u : Fin 16 → ScalarField} {g : PhysicalField}
    (hu : HasWeakGradient u g) : meanField g = 0 := by
  ext j
  rcases j with ⟨i, a⟩
  exact (component_mean_eq_coordinate g i a).symm.trans (hu.component_mean_zero i a)

theorem gradientSpace_mean_zero (g : PhysicalField) (hg : g ∈ gradientSpace) :
    meanField g = 0 := by
  have hsubset : weakGradientSpace ≤ (meanField : PhysicalField →L[ℝ] PhysicalGradient).ker := by
    rintro h ⟨u, hu⟩
    exact hu.mean_zero
  have hclosed := (meanField : PhysicalField →L[ℝ] PhysicalGradient).isClosed_ker
  exact weakGradientSpace.topologicalClosure_minimal hsubset hclosed hg

end HierarchicalLaminates.Periodic
