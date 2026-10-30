module

public import HierarchicalLaminates.GClosure.ObliqueLocalization

/-!
# Recovery coefficients and exact fractions in periodic oblique coordinates
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open MeasureTheory Set HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material
  HierarchicalLaminates.Homogenization HierarchicalLaminates.Composition

def TorusCoordinates.pullFraction (R : TorusCoordinates) (b : PhaseFraction) : PhaseFraction where
  value q := b.value (R.equiv q)
  measurable := b.measurable.comp R.continuous.measurable
  lower _ := b.lower _
  upper _ := b.upper _

theorem TorusCoordinates.pullFraction_mean (R : TorusCoordinates) (b : PhaseFraction) :
    phaseMean (R.pullFraction b) = phaseMean b :=
  R.integral b.value b.measurable

theorem TorusCoordinates.pullFraction_binary (R : TorusCoordinates) (b : PhaseFraction)
    (hb : IsBinary b) : IsBinary (R.pullFraction b) := fun _ => hb _

def obliqueRecoveryCoordinates (R : TorusCoordinates) (a : ℝ) (r k : ℕ)
    (q : Domain) : Domain :=
  matrixTorus R.inverse (recoveryCoordinates a r k (R.equiv q))

theorem obliqueRecoveryCoordinates_measurable (R : TorusCoordinates) (a : ℝ) (r k : ℕ) :
    Measurable (obliqueRecoveryCoordinates R a r k) :=
  (matrixTorus_continuous R.inverse).measurable.comp
    ((recoveryCoordinates_measurable a r k).comp R.continuous.measurable)

def obliqueRecoveryFraction (R : TorusCoordinates) (b : PhaseFraction) (a : ℝ)
    (r k : ℕ) (i : ℝ) (hi : i ∈ Icc (0 : ℝ) 1) : PhaseFraction :=
  R.pullFraction (recoveryFraction (R.symm.pullFraction b) a r k i hi)

theorem obliqueRecoveryFraction_value (R : TorusCoordinates) (b : PhaseFraction) (a : ℝ)
    (r k : ℕ) (i : ℝ) (hi : i ∈ Icc (0 : ℝ) 1) (q : Domain) :
    (obliqueRecoveryFraction R b a r k i hi).value q =
      if HierarchicalLaminates.Binary.coordinateRepresentative 1 (R.equiv q) < a then
        b.value (obliqueRecoveryCoordinates R a r k q) else i := rfl

theorem obliqueRecoveryFraction_mean (R : TorusCoordinates) (b : PhaseFraction)
    {a : ℝ} (ha : a ∈ Ioc (0 : ℝ) 1) {r k : ℕ} (hr : 0 < r) (hk : 0 < k)
    (i : ℝ) (hi : i ∈ Icc (0 : ℝ) 1) :
    phaseMean (obliqueRecoveryFraction R b a r k i hi) =
      a * phaseMean b + (1-a) * i := by
  rw [obliqueRecoveryFraction,R.pullFraction_mean,recoveryFraction_mean _ ha hr hk,
    R.symm.pullFraction_mean]

theorem obliqueRecoveryFraction_binary (R : TorusCoordinates) (b : PhaseFraction)
    (hb : IsBinary b) (a : ℝ) (r k : ℕ) (i : ℝ) (hi : i ∈ Icc (0 : ℝ) 1)
    (hiBinary : i = 0 ∨ i = 1) : IsBinary (obliqueRecoveryFraction R b a r k i hi) :=
  R.pullFraction_binary _
    (recoveryFraction_isBinary _ (R.symm.pullFraction_binary b hb) a r k i hi hiBinary)

theorem spatialGradientMap_inverse (R : TorusCoordinates) (v : PhysicalGradient) :
    spatialGradientMap R.matrix (spatialGradientMap R.inverse v) = v := by
  have h := congrArg (fun T : PhysicalGradient →L[ℝ] PhysicalGradient => T v)
    (spatialGradientMap_comp R.matrix R.inverse)
  rw [R.inverse_mul,spatialGradientMap_one] at h
  exact h

theorem obliqueSlabField_coe (R : TorusCoordinates) (a : ℝ) (r k : ℕ)
    (u : RegularPotential) :
    obliqueSlabField R a r k u =ᵐ[domainMeasure] fun q =>
      if HierarchicalLaminates.Binary.coordinateRepresentative 1 (R.equiv q) < a then
        u.gradient (obliqueRecoveryCoordinates R a r k q) else 0 := by
  filter_upwards [R.gradientPullback_coe ((transformPotential R.inverse u).slabField a r k),
    R.measurePreserving.quasiMeasurePreserving.ae
      ((transformPotential R.inverse u).slabField_coe a r k)] with q hp hs
  rw [show obliqueSlabField R a r k u q =
    R.gradientPullback ((transformPotential R.inverse u).slabField a r k) q from rfl,
    hp,hs]
  unfold slabPhysicalValue
  split_ifs with hq
  · rw [transformPotential_gradient,spatialGradientMap_inverse]
    rfl
  · exact map_zero _

end HierarchicalLaminates.GClosure
