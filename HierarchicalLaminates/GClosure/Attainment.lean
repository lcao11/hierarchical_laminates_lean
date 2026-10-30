module

public import HierarchicalLaminates.Periodic.Attainment
public import HierarchicalLaminates.GClosure.DimensionPeriod

/-!
# Attainment for the constructed constituents in every dimension

The sixteen-component cell solver supplies a zero-mean periodic weak H¹
minimizer for each phase arrangement. Adding zero potentials in passive
components and reindexing gives minimizers for every component count `m ≥ 16`.
Zero potentials minimize the passive energy terms at their constant loadings.

Rescaling the potential by a positive period preserves its gradient loading
and the normalized cell energy. The final results therefore give attained
minima on every positive-period torus for these constructed constituents.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open MeasureTheory
open HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material
  HierarchicalLaminates.Analysis HierarchicalLaminates.Lamination

/-- The zero-mean sixteen-component minimizer, expressed in the generic
weak-potential interface used for changes of component count. -/
def sixteenCellPotential (b : PhaseFraction) (F : Gradient (Fin 16)) : WeakPotential (Fin 16) :=
  WeakPotential.ofSixteen (cellPotential (coefficientLaw b) (1/4) (by norm_num)
    (coefficientLaw_coercive b) (physicalLoading F))

theorem sixteenCellPotential_mean_zero (b : PhaseFraction) (F : Gradient (Fin 16)) (a : Fin 16) :
    meanField ((sixteenCellPotential b F).potential a) = 0 :=
  cellPotential_mean_zero _ _ _ _ _ a

theorem sixteenCellPotential_energy (b : PhaseFraction) (F : Gradient (Fin 16)) :
    genericFieldEnergy phaseZero (phaseOne rho) b F (sixteenCellPotential b F) =
      genericCellEnergy phaseZero (phaseOne rho) b F := by
  rw [genericFieldEnergy_sixteen, genericCellEnergy_sixteen]
  change fieldEnergy (coefficientLaw b) (physicalLoading F)
    (WeakPotential.ofSixteen _).toSixteen.gradient = _
  rw [toSixteen_ofSixteen_gradient]
  exact cellPotential_energy _ (coefficientLaw_symmetric b) _ _ _ _

/-- Extend the active minimizer by zero potentials in the passive components. -/
def extendedCellPotential {β : Type*} (b : PhaseFraction) (F : Gradient (Fin 16 ⊕ β)) :
    WeakPotential (Fin 16 ⊕ β) :=
  (sixteenCellPotential b (leftGradient F)).join (WeakPotential.zero β)

theorem extendedCellPotential_mean_zero {β : Type*} (b : PhaseFraction)
    (F : Gradient (Fin 16 ⊕ β)) (a : Fin 16 ⊕ β) :
    meanField ((extendedCellPotential b F).potential a) = 0 := by
  cases a with
  | inl a => exact sixteenCellPotential_mean_zero b (leftGradient F) a
  | inr a => exact map_zero _

/-- The active minimizer and constant passive loading attain the extended cell energy. -/
theorem extendedCellPotential_energy {β : Type*} [Fintype β] (b : PhaseFraction)
    (F : Gradient (Fin 16 ⊕ β)) :
    genericFieldEnergy (extendTensor phaseZero) (extendTensor (phaseOne rho)) b F
      (extendedCellPotential b F) =
        genericCellEnergy (extendTensor phaseZero) (extendTensor (phaseOne rho)) b F := by
  rw [genericFieldEnergy_extend, genericCellEnergy_extend]
  have hl : (extendedCellPotential b F).restrict Sum.inl = sixteenCellPotential b (leftGradient F) := by
    apply WeakPotential.ext <;> rfl
  rw [hl, sixteenCellPotential_energy]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  simp only [affineComponent, extendedCellPotential, WeakPotential.join, WeakPotential.zero,
    add_zero, constantField_norm, Real.norm_eq_abs, sq_abs]
  rfl

/-- Reindex the active and passive components as `Fin m`, with `m ≥ 16`. -/
def dimensionCellPotential (m : ℕ) (hm : 16 ≤ m) (b : PhaseFraction) (F : Gradient (Fin m)) :
    WeakPotential (Fin m) :=
  (extendedCellPotential b (reindexGradient (dimensionEquiv m hm).symm F)).restrict
    (dimensionEquiv m hm).symm

theorem dimensionCellPotential_mean_zero (m : ℕ) (hm : 16 ≤ m) (b : PhaseFraction)
    (F : Gradient (Fin m)) (a : Fin m) :
    meanField ((dimensionCellPotential m hm b F).potential a) = 0 :=
  extendedCellPotential_mean_zero b _ _

/-- The m-component Sobolev infimum is attained by a weak periodic potential. -/
theorem dimensionCellPotential_energy (m : ℕ) (hm : 16 ≤ m) (b : PhaseFraction)
    (F : Gradient (Fin m)) :
    genericFieldEnergy (dimensionPhaseZero m hm) (dimensionPhaseOne m hm) b F
      (dimensionCellPotential m hm b F) =
        genericCellEnergy (dimensionPhaseZero m hm) (dimensionPhaseOne m hm) b F := by
  have h := genericFieldEnergy_reindex (dimensionEquiv m hm)
    (extendTensor phaseZero) (extendTensor (phaseOne rho)) b
    (reindexGradient (dimensionEquiv m hm).symm F)
    (extendedCellPotential b (reindexGradient (dimensionEquiv m hm).symm F))
  rw [reindexGradient_symm] at h
  change genericFieldEnergy (reindexTensor (dimensionEquiv m hm) (extendTensor phaseZero))
    (reindexTensor (dimensionEquiv m hm) (extendTensor (phaseOne rho))) b F _ = _
  dsimp only [dimensionCellPotential]
  rw [h, extendedCellPotential_energy]
  symm
  unfold dimensionPhaseZero dimensionPhaseOne
  have ht := genericCellEnergy_reindex (dimensionEquiv m hm)
    (extendTensor phaseZero) (extendTensor (phaseOne rho)) b
    (reindexGradient (dimensionEquiv m hm).symm F)
  rwa [reindexGradient_symm] at ht

set_option maxHeartbeats 1000000 in
/-- The unit-period cell energy is the minimum over all periodic weak H¹ potentials. -/
theorem dimensionCellEnergy_isLeast (m : ℕ) (hm : 16 ≤ m) (b : PhaseFraction)
    (F : Gradient (Fin m)) :
    IsLeast (Set.range (genericFieldEnergy (dimensionPhaseZero m hm) (dimensionPhaseOne m hm) b F))
      (genericCellEnergy (dimensionPhaseZero m hm) (dimensionPhaseOne m hm) b F) := by
  refine ⟨⟨dimensionCellPotential m hm b F, dimensionCellPotential_energy m hm b F⟩, ?_⟩
  rintro E ⟨v, rfl⟩
  have h := genericFieldEnergy_reindex (dimensionEquiv m hm)
    (extendTensor phaseZero) (extendTensor (phaseOne rho)) b
    (reindexGradient (dimensionEquiv m hm).symm F) (v.restrict (dimensionEquiv m hm))
  rw [reindexGradient_symm, WeakPotential.restrict_inverse] at h
  change genericCellEnergy (reindexTensor (dimensionEquiv m hm) (extendTensor phaseZero))
    (reindexTensor (dimensionEquiv m hm) (extendTensor (phaseOne rho))) b F ≤ _
  dsimp only [dimensionPhaseZero, dimensionPhaseOne]
  have ht := genericCellEnergy_reindex (dimensionEquiv m hm)
    (extendTensor phaseZero) (extendTensor (phaseOne rho)) b
    (reindexGradient (dimensionEquiv m hm).symm F)
  rw [reindexGradient_symm] at ht
  rw [h, ht, genericCellEnergy_extend]
  exact genericFieldEnergy_extend_lower b _ _

variable (L : ℝ) [Fact (0 < L)]

/-- Push the unit-period minimizer to period `L`, scaling its values by `L`
preserving the prescribed affine gradient. -/
def dimensionPeriodCellPotential (m : ℕ) (hm : 16 ≤ m) (b : PhaseFraction)
    (F : Gradient (Fin m)) : PeriodWeakPotential L (Fin m) :=
  (dimensionCellPotential m hm b F).pushPeriod L

/-- Positive-period rescaling preserves the zero-mean normalization. -/
theorem dimensionPeriodCellPotential_mean_zero (m : ℕ) (hm : 16 ≤ m) (b : PhaseFraction)
    (F : Gradient (Fin m)) (a : Fin m) :
    (∫ y, (dimensionPeriodCellPotential L m hm b F).potential a y ∂periodMeasure L) = 0 := by
  let u := (dimensionCellPotential m hm b F).potential a
  have he : (dimensionPeriodCellPotential L m hm b F).potential a =ᵐ[periodMeasure L]
      fun y => L*u ((scaleTorus L).symm y) := by
    filter_upwards [Lp.coeFn_smul L (pushField L u), pushField_coe L u] with y hs hp
    change (L • pushField L u) y = _
    rw [hs]
    change L*(pushField L u y) = L*u ((scaleTorus L).symm y)
    rw [hp]
  rw [integral_congr_ae he, integral_const_mul, integral_unscaling,
    ← meanField_eq_integral]
  change L*meanField ((dimensionCellPotential m hm b F).potential a) = 0
  rw [dimensionCellPotential_mean_zero, mul_zero]

theorem dimensionPeriodCellPotential_energy (m : ℕ) (hm : 16 ≤ m) (b : PhaseFraction)
    (F : Gradient (Fin m)) :
    genericPeriodFieldEnergy L (dimensionPhaseZero m hm) (dimensionPhaseOne m hm) b F
      (dimensionPeriodCellPotential L m hm b F) =
        genericPeriodCellEnergy L (dimensionPhaseZero m hm) (dimensionPhaseOne m hm) b F := by
  change genericPeriodFieldEnergy L _ _ b F ((dimensionCellPotential m hm b F).pushPeriod L) = _
  rw [genericPeriodFieldEnergy_pull, pull_pushPeriod, dimensionCellPotential_energy,
    genericPeriodCellEnergy_transport]

/-- Minimizing weak potentials exist on every positive-period cell. -/
theorem dimensionPeriodCellEnergy_attained (m : ℕ) (hm : 16 ≤ m) (b : PhaseFraction)
    (F : Gradient (Fin m)) :
    ∃ u : PeriodWeakPotential L (Fin m),
      genericPeriodFieldEnergy L (dimensionPhaseZero m hm) (dimensionPhaseOne m hm) b F u =
        genericPeriodCellEnergy L (dimensionPhaseZero m hm) (dimensionPhaseOne m hm) b F := by
  exact ⟨dimensionPeriodCellPotential L m hm b F, dimensionPeriodCellPotential_energy L m hm b F⟩

/-- The normalized positive-period cell energy is the least energy over all
periodic weak H¹ competitors on that torus. -/
theorem dimensionPeriodCellEnergy_isLeast (m : ℕ) (hm : 16 ≤ m) (b : PhaseFraction)
    (F : Gradient (Fin m)) :
    IsLeast (Set.range (genericPeriodFieldEnergy L
      (dimensionPhaseZero m hm) (dimensionPhaseOne m hm) b F))
      (genericPeriodCellEnergy L (dimensionPhaseZero m hm) (dimensionPhaseOne m hm) b F) := by
  obtain ⟨u, hu⟩ := dimensionPeriodCellEnergy_attained L m hm b F
  refine ⟨⟨u, hu⟩, ?_⟩
  rintro E ⟨v, rfl⟩
  rw [genericPeriodCellEnergy_transport, genericPeriodFieldEnergy_pull]
  exact (dimensionCellEnergy_isLeast m hm b F).2 (Set.mem_range_self (v.pull L))

end HierarchicalLaminates.GClosure
