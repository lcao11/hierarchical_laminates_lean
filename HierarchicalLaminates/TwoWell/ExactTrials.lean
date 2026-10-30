module

public import HierarchicalLaminates.Periodic.Attainment
public import HierarchicalLaminates.TwoWell.H1Trial32
public import HierarchicalLaminates.TwoWell.Gap
public import HierarchicalLaminates.GClosure.DimensionEnergy

/-!
# Exact weak H¹ correctors and the paired two-well trial

Subtracting the mean of an L² equilibrium flux and rotating its two spatial
rows gives the gradient of a zero-mean periodic weak H¹ stream potential.
Joining this stream potential to a primal cell corrector gives one
thirty-two-component weak H¹ trial.

Both fields use the same phase arrangement. For binary arrangements, the
selected primal and complementary quadratic energies equal the two cell
energies. The weak-H¹ trial inequality then gives the quasiconvex upper bound
and the quantitative comparison with the rank-one convex envelope.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.TwoWell

open MeasureTheory Matrix
open HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material
  HierarchicalLaminates.Analysis HierarchicalLaminates.Lamination HierarchicalLaminates.GClosure

/-- Rotation of a mean-zero equilibrium fluctuation belongs to the closed gradient space. -/
theorem equilibrium_rotation_admissible (j : PhysicalField)
    (hj : ∀ g ∈ gradientSpace, inner ℝ j g = 0) :
    rotateField j-constantField (rotatePhysical (meanField j)) ∈ gradientSpace := by
  have hm : meanField (j-constantField (meanField j)) = 0 := by
    rw [map_sub, mean_constantField, sub_self]
  have ho (g : PhysicalField) (hg : g ∈ gradientSpace) :
      inner ℝ (j-constantField (meanField j)) g = 0 := by
    rw [inner_sub_left, hj g hg, constant_mean_pairing,
      gradientSpace_mean_zero g hg, inner_zero_right, sub_self]
  have h := rotate_equilibrium_mem_gradientSpace _ hm ho
  rwa [map_sub, rotateField_constant] at h

/-- A periodic H¹ stream potential for the mean-zero part of an L² equilibrium flux. -/
def streamPotential (j : PhysicalField)
    (hj : ∀ g ∈ gradientSpace, inner ℝ j g = 0) : SobolevPotential :=
  exactPotential (rotateField j-constantField (rotatePhysical (meanField j)))
    (equilibrium_rotation_admissible j hj)

theorem streamPotential_mean_zero (j : PhysicalField)
    (hj : ∀ g ∈ gradientSpace, inner ℝ j g = 0) (a : Fin 16) :
    meanField ((streamPotential j hj).potential a) = 0 :=
  exactPotential_mean_zero _ _ a

/-- The rotated flux splits into its rotated mean and the stream gradient. -/
theorem streamPotential_representation (j : PhysicalField)
    (hj : ∀ g ∈ gradientSpace, inner ℝ j g = 0) :
    constantField (rotatePhysical (meanField j))+(streamPotential j hj).gradient =
      rotateField j := by
  change constantField (rotatePhysical (meanField j))+
    (rotateField j-constantField (rotatePhysical (meanField j))) = rotateField j
  abel

/-- The zero-mean minimizing potential for the primal coefficient law. -/
def primalCellPotential (b : PhaseFraction) (f : PhysicalGradient) : SobolevPotential :=
  cellPotential (coefficientLaw b) (1/4) (by norm_num) (coefficientLaw_coercive b) f

theorem primalCellPotential_representation (b : PhaseFraction) (f : PhysicalGradient) :
    constantField f+(primalCellPotential b f).gradient = exactCellField b f := rfl

/-- The stream potential of the cell flux at loading `η`, using the same
phase arrangement as the primal coefficient law. -/
def cellStreamPotential (b : PhaseFraction) (η : PhysicalGradient) : SobolevPotential :=
  streamPotential (coefficientLaw b (exactCellField b η)) (exactCellField_isCell b η).2

theorem cellStreamPotential_representation (b : PhaseFraction) (η : PhysicalGradient) :
    constantField (rotatePhysical (HierarchicalLaminates.Material.effectiveOperator b η))+
      (cellStreamPotential b η).gradient =
        rotateField (coefficientLaw b (exactCellField b η)) :=
  streamPotential_representation _ _

/-- Joining two weak sixteen-component potentials gives one 32-component potential. -/
def joinWeak32 (u v : SobolevPotential) : WeakPotential (Fin 32) :=
  ((WeakPotential.ofSixteen u).join (WeakPotential.ofSixteen v)).restrict componentSumEquiv.symm

theorem joinWeak32_mean_zero (u v : SobolevPotential)
    (hu : ∀ a, meanField (u.potential a) = 0)
    (hv : ∀ a, meanField (v.potential a) = 0) (a : Fin 32) :
    meanField ((joinWeak32 u v).potential a) = 0 := by
  obtain ⟨a, rfl⟩ := componentSumEquiv.surjective a
  cases a with
  | inl a => simpa [joinWeak32, WeakPotential.restrict, WeakPotential.join,
      WeakPotential.ofSixteen] using hu a
  | inr a => simpa [joinWeak32, WeakPotential.restrict, WeakPotential.join,
      WeakPotential.ofSixteen] using hv a

theorem leftWeak32_join_gradient (u v : SobolevPotential) :
    (leftWeak32 (joinWeak32 u v)).gradient = u.gradient := by
  change assembleComponents _ = u.gradient
  rw [← assembleComponents_components u.gradient]
  congr 1
  funext c
  rcases c with ⟨i, a⟩
  simp [joinWeak32, WeakPotential.restrict, WeakPotential.join,
    WeakPotential.ofSixteen]

theorem rightWeak32_join_gradient (u v : SobolevPotential) :
    (rightWeak32 (joinWeak32 u v)).gradient = v.gradient := by
  change assembleComponents _ = v.gradient
  rw [← assembleComponents_components v.gradient]
  congr 1
  funext c
  rcases c with ⟨i, a⟩
  simp [joinWeak32, WeakPotential.restrict, WeakPotential.join,
    WeakPotential.ofSixteen]

theorem joinWeak32_trial_integral (F : Gradient32) (u v : SobolevPotential) :
    (∫ q, twoWellEnergy32 (fun c => F c+(joinWeak32 u v).gradient c q) ∂domainMeasure) =
      ∫ q, twoWellEnergy (weakTrial (split32 F) u v q) ∂domainMeasure := by
  apply integral_congr_ae
  filter_upwards [weakTrial32_components F (joinWeak32 u v)] with q hq
  rw [twoWellEnergy32_eq, ← hq]
  simp only [weakTrial, leftWeak32_join_gradient, rightWeak32_join_gradient]

/-- For a binary arrangement, the pointwise two-well minimum is bounded by
the quadratic branch selected by that arrangement. -/
theorem twoWellIntegral_le_selected (b : PhaseFraction)
    (hb : ∀ q, b.value q = 0 ∨ b.value q = 1) (e g : PhysicalField) :
    twoWellIntegral (e,g) ≤ selectedPairEnergy b e g := by
  rw [twoWellIntegral, selectedPairEnergy_eq_integral b hb]
  apply integral_mono_ae (twoWellEnergy_integrable_fields e g)
    (selectedPairEnergy_integrable b hb e g)
  exact Filter.Eventually.of_forall (fun q => twoWellEnergy_le_selected b hb q _)

/-- The paired mean consists of the primal loading and the rotated effective
flux associated with the complementary loading `η`. -/
def exactPairMean (b : PhaseFraction) (f η : PhysicalGradient) : PairedGradient :=
  ((f : Gradient16), (rotatePhysical (HierarchicalLaminates.Material.effectiveOperator b η) : Gradient16))

theorem exactPair_trial_integral (b : PhaseFraction) (f η : PhysicalGradient) :
    (∫ q, twoWellEnergy (weakTrial (exactPairMean b f η)
      (primalCellPotential b f) (cellStreamPotential b η) q) ∂domainMeasure) =
      twoWellIntegral (exactCellField b f,
        rotateField (coefficientLaw b (exactCellField b η))) := by
  rw [← weakTrial_twoWellIntegral]
  change twoWellIntegral (constantField f+(primalCellPotential b f).gradient,
    constantField (rotatePhysical (HierarchicalLaminates.Material.effectiveOperator b η))+
      (cellStreamPotential b η).gradient) = _
  rw [primalCellPotential_representation, cellStreamPotential_representation]

/-- The exact H¹ pair has the same selected quadratic energy as the two cell problems. -/
theorem exactPair_selected_energy (b : PhaseFraction)
    (hb : ∀ q, b.value q = 0 ∨ b.value q = 1) (f η : PhysicalGradient) :
    selectedPairEnergy b
      (constantField f+(primalCellPotential b f).gradient)
      (constantField (rotatePhysical (HierarchicalLaminates.Material.effectiveOperator b η))+
        (cellStreamPotential b η).gradient) =
      quadraticEnergy (effectiveMatrix b) (f : Gradient16)+
        quadraticEnergy (effectiveMatrix b) (η : Gradient16) := by
  rw [primalCellPotential_representation, cellStreamPotential_representation]
  exact selectedPairEnergy_exact_fields b hb f η

/-- Join the primal and stream potentials as one 32-component weak H¹ trial. -/
def exactPairPotential32 (b : PhaseFraction) (f η : PhysicalGradient) : WeakPotential (Fin 32) :=
  joinWeak32 (primalCellPotential b f) (cellStreamPotential b η)

theorem exactPairPotential32_mean_zero (b : PhaseFraction) (f η : PhysicalGradient) (a : Fin 32) :
    meanField ((exactPairPotential32 b f η).potential a) = 0 :=
  joinWeak32_mean_zero _ _ (cellPotential_mean_zero _ _ _ _ _)
    (streamPotential_mean_zero _ _) a

/-- The two-well energy of the joined trial is at most the sum of the two
cell energies for a binary phase arrangement. -/
theorem exactPairPotential32_energy_upper (b : PhaseFraction)
    (hb : ∀ q, b.value q = 0 ∨ b.value q = 1) (f η : PhysicalGradient) :
    (∫ q, twoWellEnergy32 (fun c => join32 (exactPairMean b f η) c+
      (exactPairPotential32 b f η).gradient c q) ∂domainMeasure) ≤
        quadraticEnergy (effectiveMatrix b) (f : Gradient16)+
          quadraticEnergy (effectiveMatrix b) (η : Gradient16) := by
  rw [exactPairPotential32, joinWeak32_trial_integral, split32_join32,
    exactPair_trial_integral]
  exact (twoWellIntegral_le_selected b hb _ _).trans_eq (selectedPairEnergy_exact_fields b hb f η)

/-- The 32-component weak H¹ trial bounds the quasiconvex envelope
at its paired mean. -/
theorem quasiconvex_upper_exact_pair (b : PhaseFraction)
    (hb : ∀ q, b.value q = 0 ∨ b.value q = 1) (f η : PhysicalGradient) :
    quasiconvexEnvelope32 twoWellEnergy32 (join32 (exactPairMean b f η)) ≤
      quadraticEnergy (effectiveMatrix b) (f : Gradient16)+
        quadraticEnergy (effectiveMatrix b) (η : Gradient16) :=
  (quasiconvex_h1_trial_inequality32_weak _ (exactPairPotential32 b f η)).trans
    (exactPairPotential32_energy_upper b hb f η)

theorem exactPairMean_application (b : PhaseFraction) :
    exactPairMean b (WithLp.toLp 2 xiFlat) (WithLp.toLp 2 etaFlat) = applicationMean b := by
  apply Prod.ext
  · rfl
  · change (rotatePhysical (HierarchicalLaminates.Material.effectiveOperator b
      (WithLp.toLp 2 etaFlat)) : Gradient16) = rotate (effectiveMatrix b *ᵥ etaFlat)
    rw [rotatePhysical_apply]
    congr 1
    rw [← effectiveMatrix_operator]
    rfl

/-- Specializing to the fixed loadings gives the quasiconvex upper bound at
`applicationMean b`. -/
theorem quasiconvex_upper_via_exact_h1 (b : PhaseFraction)
    (hb : ∀ q, b.value q = 0 ∨ b.value q = 1) :
    quasiconvexEnvelope twoWellEnergy (applicationMean b) ≤
      quadraticEnergy (effectiveMatrix b) xiFlat+quadraticEnergy (effectiveMatrix b) etaFlat := by
  have h := quasiconvex_upper_exact_pair b hb (WithLp.toLp 2 xiFlat) (WithLp.toLp 2 etaFlat)
  rwa [exactPairMean_application, twoWell_quasiconvexEnvelope32] at h

/-- The exact weak H¹ trial bounds the difference of the two envelopes below
by `physicalLoadingDifference b`, for every binary phase arrangement. -/
theorem quantitative_gap_via_exact_h1 (b : PhaseFraction)
    (hb : ∀ q, b.value q = 0 ∨ b.value q = 1) :
    physicalLoadingDifference b ≤
      rankOneEnvelope twoWellEnergy (applicationMean b)-
        quasiconvexEnvelope twoWellEnergy (applicationMean b) := by
  have hu := quasiconvex_upper_via_exact_h1 b hb
  rw [application_energy_identity] at hu
  have hl := rankOne_lower (applicationFlux b)
  change 2*(etaFlat ⬝ᵥ applicationFlux b) ≤ rankOneEnvelope twoWellEnergy (applicationMean b) at hl
  linarith

/-- A positive loading difference makes the envelope separation strict. -/
theorem strict_gap_via_exact_h1 (b : PhaseFraction)
    (hb : ∀ q, b.value q = 0 ∨ b.value q = 1)
    (hgap : 0 < physicalLoadingDifference b) :
    quasiconvexEnvelope twoWellEnergy (applicationMean b) <
      rankOneEnvelope twoWellEnergy (applicationMean b) :=
  sub_pos.mp (hgap.trans_le (quantitative_gap_via_exact_h1 b hb))

end HierarchicalLaminates.TwoWell
