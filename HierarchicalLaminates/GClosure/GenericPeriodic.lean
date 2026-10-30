module

public import HierarchicalLaminates.GClosure.Interfaces

/-!
# Periodic weak potentials with an arbitrary finite component index
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open MeasureTheory HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material
  HierarchicalLaminates.Lamination

abbrev ComponentIndex (α : Type*) := Fin 2 × α

/-- The distributional derivative identity for each potential component. -/
structure WeakPotential (α : Type*) where
  potential : α → ScalarField
  gradient : ComponentIndex α → ScalarField
  weak : ∀ (i : Fin 2) (a : α) (test : SmoothTest),
    inner ℝ (gradient (i,a)) (continuousField test.value) =
      -inner ℝ (potential a) (continuousField (test.derivative i))

@[ext] theorem WeakPotential.ext {α : Type*} {u v : WeakPotential α}
    (hu : u.potential = v.potential) (hg : u.gradient = v.gradient) : u = v := by
  cases u
  cases v
  cases hu
  cases hg
  rfl

def WeakPotential.zero (α : Type*) : WeakPotential α where
  potential := fun _ => 0
  gradient := fun _ => 0
  weak := by intros; simp

instance (α : Type*) : Nonempty (WeakPotential α) := ⟨WeakPotential.zero α⟩

def WeakPotential.restrict {α β : Type*} (u : WeakPotential α) (f : β → α) :
    WeakPotential β where
  potential := fun a => u.potential (f a)
  gradient := fun c => u.gradient (c.1, f c.2)
  weak := fun i a test => u.weak i (f a) test

theorem WeakPotential.gradient_mean_zero {α : Type*} (u : WeakPotential α)
    (c : ComponentIndex α) : meanField (u.gradient c) = 0 := by
  have h := u.weak c.1 c.2 (constantTest 1)
  simp only [constantTest, continuousField_const, map_zero, inner_zero_right, neg_zero] at h
  have hp := constant_mean_pairing (1 : ℝ) (u.gradient c)
  rw [real_inner_comm] at h
  simpa only [Real.inner_apply, one_mul] using hp.symm.trans h

def affineComponent {α : Type*} (F : Gradient α) (u : WeakPotential α)
    (c : ComponentIndex α) : ScalarField := constantField (F c) + u.gradient c

theorem affineComponent_norm_sq {α : Type*} (F : Gradient α) (u : WeakPotential α)
    (c : ComponentIndex α) :
    ‖affineComponent F u c‖ ^ 2 = (F c) ^ 2 + ‖u.gradient c‖ ^ 2 := by
  have hc : inner ℝ (constantField (F c)) (u.gradient c) = 0 := by
    rw [constant_mean_pairing, u.gradient_mean_zero, inner_zero_right]
  rw [affineComponent, norm_add_sq_real, hc, constantField_norm, Real.norm_eq_abs, sq_abs]
  ring

def scalarLaw (c₀ c₁ : ℝ) (b : PhaseFraction) (f : ScalarField) : ScalarField :=
  c₀ • f + (c₁-c₀) • scalarMultiplication b.bounded f

theorem scalarLaw_coe (c₀ c₁ : ℝ) (b : PhaseFraction) (f : ScalarField) :
    scalarLaw c₀ c₁ b f =ᵐ[domainMeasure] fun q =>
      (c₀+b.value q*(c₁-c₀))*f q := by
  filter_upwards [Lp.coeFn_add (c₀ • f) ((c₁-c₀) • scalarMultiplication b.bounded f),
    Lp.coeFn_smul c₀ f, Lp.coeFn_smul (c₁-c₀) (scalarMultiplication b.bounded f),
    scalarMultiplication_coe b.bounded f] with q hadd hc₀ hc₁ hb
  rw [scalarLaw, hadd]
  simp only [Pi.add_apply]
  rw [hc₀, hc₁]
  simp only [Pi.smul_apply]
  rw [hb]
  simp only [smul_eq_mul]
  change c₀ * f q + (c₁-c₀) * (b.value q * f q) = _
  ring

theorem scalarLaw_inner_integral (c₀ c₁ : ℝ) (b : PhaseFraction) (f g : ScalarField) :
    inner ℝ (scalarLaw c₀ c₁ b f) g =
      ∫ q, (c₀+b.value q*(c₁-c₀))*f q*g q ∂domainMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [scalarLaw_coe c₀ c₁ b f] with q hq
  rw [hq]
  simp only [Real.inner_apply]

theorem scalarLaw_integrable (c₀ c₁ : ℝ) (b : PhaseFraction) (f g : ScalarField) :
    Integrable (fun q => (c₀+b.value q*(c₁-c₀))*f q*g q) domainMeasure := by
  apply (L2.integrable_inner (scalarLaw c₀ c₁ b f) g).congr
  filter_upwards [scalarLaw_coe c₀ c₁ b f] with q hq
  rw [hq]
  simp only [Real.inner_apply]

def genericFieldEnergy {α : Type*} [Fintype α] (L₀ L₁ : Tensor α) (b : PhaseFraction)
    (F : Gradient α) (u : WeakPotential α) : ℝ :=
  ∑ c : ComponentIndex α, ∑ d : ComponentIndex α,
    inner ℝ (scalarLaw (L₀ c d) (L₁ c d) b (affineComponent F u d))
      (affineComponent F u c)

def genericCellEnergy {α : Type*} [Fintype α] (L₀ L₁ : Tensor α) (b : PhaseFraction)
    (F : Gradient α) : ℝ :=
  sInf (Set.range (genericFieldEnergy L₀ L₁ b F))

/-- The cell quadratic form equals the integral energy of the binary mixture. -/
theorem genericFieldEnergy_eq_integral {α : Type*} [Fintype α]
    (L₀ L₁ : Tensor α) (b : PhaseFraction) (F : Gradient α) (u : WeakPotential α) :
    genericFieldEnergy L₀ L₁ b F u =
      ∫ q, quadraticEnergy (L₀+b.value q • (L₁-L₀))
        (fun c => F c + u.gradient c q) ∂domainMeasure := by
  have he (c : ComponentIndex α) : affineComponent F u c =ᵐ[domainMeasure]
      fun q => F c + u.gradient c q := by
    filter_upwards [Lp.coeFn_add (constantField (F c)) (u.gradient c),
      Lp.coeFn_const 2 domainMeasure (F c)] with q hadd hc
    change constantField (F c) q = F c at hc
    rw [affineComponent, hadd]
    simp only [Pi.add_apply]
    rw [hc]
  have hs : (∑ c : ComponentIndex α, ∑ d : ComponentIndex α,
      inner ℝ (scalarLaw (L₀ c d) (L₁ c d) b (affineComponent F u d))
        (affineComponent F u c)) =
      ∫ q, ∑ c : ComponentIndex α, ∑ d : ComponentIndex α,
        (L₀ c d+b.value q*(L₁ c d-L₀ c d))*
          affineComponent F u d q*affineComponent F u c q ∂domainMeasure := by
    simp_rw [scalarLaw_inner_integral]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro c _
      rw [integral_finsetSum]
      exact fun d _ => scalarLaw_integrable _ _ _ _ _
    · intro c _
      exact integrable_finsetSum _ (fun d _ => scalarLaw_integrable _ _ _ _ _)
  rw [genericFieldEnergy, hs]
  apply integral_congr_ae
  have heall : ∀ᵐ q ∂domainMeasure, ∀ c, affineComponent F u c q = F c+u.gradient c q := by
    simp only [Filter.eventually_all]
    exact he
  filter_upwards [heall] with q hq
  simp only [hq, quadraticEnergy, dotProduct, Matrix.mulVec, Matrix.add_apply,
    Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  ring

end HierarchicalLaminates.GClosure
