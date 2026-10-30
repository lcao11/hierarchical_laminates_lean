module

public import HierarchicalLaminates.GClosure.GenericPeriodic

/-!
# The componentwise weak space and the sixteen-component cell problem
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open MeasureTheory HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material
  HierarchicalLaminates.Lamination HierarchicalLaminates.WeakCalculus HierarchicalLaminates.Composition

def physicalCoordinate (c : Fin 2 × Fin 16) : PhysicalGradient :=
  WithLp.toLp 2 (Pi.single c (1 : ℝ))

def assembleComponents (g : (Fin 2 × Fin 16) → ScalarField) : PhysicalField :=
  ∑ c : Fin 2 × Fin 16, spanField (physicalCoordinate c) (g c)

set_option maxRecDepth 4096 in
theorem componentField_assemble (g : (Fin 2 × Fin 16) → ScalarField)
    (i : Fin 2) (a : Fin 16) : componentField i a (assembleComponents g) = g (i,a) := by
  classical
  rw [assembleComponents, map_sum]
  calc
    _ = componentField i a (spanField (physicalCoordinate (i,a)) (g (i,a))) := by
      apply Finset.sum_eq_single (i,a)
      · intro c _ hc
        rw [componentField_spanField]
        change (Pi.single c (1 : ℝ) : (Fin 2 × Fin 16) → ℝ) (i,a) • g c = 0
        rw [Pi.single_eq_of_ne (Ne.symm hc), zero_smul]
      · simp
    _ = g (i,a) := by
      rw [componentField_spanField]
      change (Pi.single (i,a) (1 : ℝ) : (Fin 2 × Fin 16) → ℝ) (i,a) • g (i,a) = g (i,a)
      rw [Pi.single_eq_same, one_smul]

theorem physicalField_ext (v w : PhysicalField)
    (h : ∀ i a, componentField i a v = componentField i a w) : v = w := by
  have hz : inner ℝ (v-w) (v-w) = 0 := by
    rw [physical_inner_components]
    simp only [map_sub, h, sub_self, inner_zero_left, Finset.sum_const_zero]
  have hn : ‖v-w‖ = 0 := by
    rw [real_inner_self_eq_norm_sq] at hz
    nlinarith [norm_nonneg (v-w)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

theorem assembleComponents_components (g : PhysicalField) :
    assembleComponents (fun c => componentField c.1 c.2 g) = g := by
  apply physicalField_ext
  intro i a
  rw [componentField_assemble]

def WeakPotential.toSixteen (u : WeakPotential (Fin 16)) : SobolevPotential where
  potential := u.potential
  gradient := assembleComponents u.gradient
  weakGradient := by
    intro i a test
    rw [componentField_assemble]
    exact u.weak i a test

def WeakPotential.ofSixteen (u : SobolevPotential) : WeakPotential (Fin 16) where
  potential := u.potential
  gradient c := componentField c.1 c.2 u.gradient
  weak := fun i a test => u.weakGradient i a test

theorem toSixteen_ofSixteen_gradient (u : SobolevPotential) :
    (WeakPotential.ofSixteen u).toSixteen.gradient = u.gradient :=
  assembleComponents_components u.gradient

theorem assembleComponents_coe (g : (Fin 2 × Fin 16) → ScalarField) :
    assembleComponents g =ᵐ[domainMeasure] fun q => WithLp.toLp 2 (fun c => g c q) := by
  have hcomp : ∀ᵐ q ∂domainMeasure, ∀ c : Fin 2 × Fin 16,
      assembleComponents g q c = g c q := by
    simp only [Filter.eventually_all]
    intro c
    have h := (EuclideanSpace.proj (𝕜 := ℝ) c).coeFn_compLpL (assembleComponents g)
    change componentField c.1 c.2 (assembleComponents g) =ᵐ[domainMeasure]
      fun q => assembleComponents g q c at h
    rw [componentField_assemble] at h
    exact h.symm
  filter_upwards [hcomp] with q hq
  ext c
  exact hq c

def physicalLoading (F : Gradient (Fin 16)) : PhysicalGradient := WithLp.toLp 2 F

theorem genericFieldEnergy_sixteen (b : PhaseFraction) (F : Gradient (Fin 16))
    (u : WeakPotential (Fin 16)) :
    genericFieldEnergy phaseZero (phaseOne rho) b F u =
      fieldEnergy (coefficientLaw b) (physicalLoading F) u.toSixteen.gradient := by
  rw [genericFieldEnergy_eq_integral]
  change _ = inner ℝ (coefficientLaw b (constantField (physicalLoading F) + u.toSixteen.gradient))
    (constantField (physicalLoading F) + u.toSixteen.gradient)
  rw [coefficientLaw_energy]
  apply integral_congr_ae
  filter_upwards [assembleComponents_coe u.gradient,
    Lp.coeFn_const 2 domainMeasure (physicalLoading F),
    Lp.coeFn_add (constantField (physicalLoading F)) u.toSixteen.gradient]
    with q hg hF hadd
  change constantField (physicalLoading F) q = physicalLoading F at hF
  change assembleComponents u.gradient q = _ at hg
  rw [hadd]
  simp only [Pi.add_apply]
  change quadraticEnergy (phaseZero + b.value q • (phaseOne rho-phaseZero))
      (fun c => F c + u.gradient c q) =
    inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (mixtureTensor (b.value q))
      (constantField (physicalLoading F) q + assembleComponents u.gradient q))
      (constantField (physicalLoading F) q + assembleComponents u.gradient q)
  rw [hF, hg, mixtureTensor_affine]
  rw [real_inner_comm, Matrix.inner_toEuclideanCLM]
  rfl

theorem genericCellEnergy_sixteen (b : PhaseFraction) (F : Gradient (Fin 16)) :
    genericCellEnergy phaseZero (phaseOne rho) b F =
      sobolevCellEnergy (coefficientLaw b) (physicalLoading F) := by
  unfold genericCellEnergy sobolevCellEnergy
  apply congrArg sInf
  ext E
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u.toSixteen, (genericFieldEnergy_sixteen b F u).symm⟩
  · rintro ⟨u, rfl⟩
    refine ⟨WeakPotential.ofSixteen u, ?_⟩
    rw [genericFieldEnergy_sixteen, toSixteen_ofSixteen_gradient]

end HierarchicalLaminates.GClosure
