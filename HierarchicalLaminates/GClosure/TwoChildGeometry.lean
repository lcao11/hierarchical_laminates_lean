module

public import HierarchicalLaminates.GClosure.ObliqueRecovery
public import HierarchicalLaminates.GClosure.SharedTranslation

/-!
# Two-phase coefficients with microscopic patterns in complementary slabs
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open MeasureTheory Set HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material
  HierarchicalLaminates.Binary HierarchicalLaminates.Homogenization HierarchicalLaminates.Composition

def obliqueComplementCoordinates (R : TorusCoordinates) (a : ℝ) (r k : ℕ)
    (q : Domain) : Domain :=
  matrixTorus R.inverse (recoveryCoordinates (1-a) r k (shiftVertical a (R.equiv q)))

theorem obliqueComplementCoordinates_measurable (R : TorusCoordinates) (a : ℝ) (r k : ℕ) :
    Measurable (obliqueComplementCoordinates R a r k) :=
  (matrixTorus_continuous R.inverse).measurable.comp
    ((recoveryCoordinates_measurable (1-a) r k).comp
      ((shiftVertical_measurable a).comp R.continuous.measurable))

def complementaryRecoveryFraction (R : TorusCoordinates) (b : PhaseFraction) (a : ℝ)
    (r k : ℕ) : PhaseFraction where
  value q := (recoveryFraction (R.symm.pullFraction b) (1-a) r k 0 (by simp)).value
    (shiftVertical a (R.equiv q))
  measurable := (recoveryFraction (R.symm.pullFraction b) (1-a) r k 0 (by simp)).measurable.comp
    ((shiftVertical_measurable a).comp R.continuous.measurable)
  lower q := (recoveryFraction (R.symm.pullFraction b) (1-a) r k 0 (by simp)).lower _
  upper q := (recoveryFraction (R.symm.pullFraction b) (1-a) r k 0 (by simp)).upper _

theorem complementaryRecoveryFraction_value (R : TorusCoordinates) (b : PhaseFraction)
    {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1) (r k : ℕ) (q : Domain) :
    (complementaryRecoveryFraction R b a r k).value q =
      if a ≤ coordinateRepresentative 1 (R.equiv q) then
        b.value (obliqueComplementCoordinates R a r k q) else 0 := by
  change (if coordinateRepresentative 1 (shiftVertical a (R.equiv q)) < 1-a then
    b.value (obliqueComplementCoordinates R a r k q) else 0) = _
  simp only [shiftVertical_slab_iff ha₀ ha₁]

theorem complementaryRecoveryFraction_binary (R : TorusCoordinates) (b : PhaseFraction)
    (hb : IsBinary b) (a : ℝ) (r k : ℕ) :
    IsBinary (complementaryRecoveryFraction R b a r k) := by
  intro q
  exact recoveryFraction_isBinary _ (R.symm.pullFraction_binary b hb)
    (1-a) r k 0 (by simp) (Or.inl rfl) _

theorem complementaryRecoveryFraction_mean (R : TorusCoordinates) (b : PhaseFraction)
    {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1) {r k : ℕ} (hr : 0 < r) (hk : 0 < k) :
    phaseMean (complementaryRecoveryFraction R b a r k) = (1-a) * phaseMean b := by
  let c := recoveryFraction (R.symm.pullFraction b) (1-a) r k 0 (by simp)
  change (∫ q, c.value (shiftVertical a (R.equiv q)) ∂domainMeasure) = _
  have hR : (∫ q, c.value (shiftVertical a (R.equiv q)) ∂domainMeasure) =
      ∫ q, c.value (shiftVertical a q) ∂domainMeasure := by
    simpa only [Function.comp_def] using
      R.integral (fun q => c.value (shiftVertical a q))
        (c.measurable.comp (shiftVertical_measurable a))
  rw [hR,shiftVertical_integral a c.value c.measurable]
  change phaseMean c = _
  dsimp only [c]
  rw [recoveryFraction_mean _ ⟨by linarith,by linarith⟩ hr hk,
    R.symm.pullFraction_mean]
  ring

def twoChildRecovery (R : TorusCoordinates) (b c : PhaseFraction) (a : ℝ)
    (r₁ k₁ r₂ k₂ : ℕ) : PhaseFraction where
  value q := if coordinateRepresentative 1 (R.equiv q) < a then
    b.value (obliqueRecoveryCoordinates R a r₁ k₁ q)
    else c.value (obliqueComplementCoordinates R a r₂ k₂ q)
  measurable := Measurable.ite
    (measurableSet_lt ((coordinateRepresentative_measurable 1).comp R.continuous.measurable)
      measurable_const)
    (b.measurable.comp (obliqueRecoveryCoordinates_measurable R a r₁ k₁))
    (c.measurable.comp (obliqueComplementCoordinates_measurable R a r₂ k₂))
  lower q := by split_ifs <;> first | exact b.lower _ | exact c.lower _
  upper q := by split_ifs <;> first | exact b.upper _ | exact c.upper _

theorem twoChildRecovery_binary (R : TorusCoordinates) (b c : PhaseFraction)
    (hb : IsBinary b) (hc : IsBinary c) (a : ℝ) (r₁ k₁ r₂ k₂ : ℕ) :
    IsBinary (twoChildRecovery R b c a r₁ k₁ r₂ k₂) := by
  intro q
  dsimp only [twoChildRecovery]
  split_ifs
  · exact hb _
  · exact hc _

theorem twoChildRecovery_value_sum (R : TorusCoordinates) (b c : PhaseFraction)
    {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1) (r₁ k₁ r₂ k₂ : ℕ) (q : Domain) :
    (twoChildRecovery R b c a r₁ k₁ r₂ k₂).value q =
      (obliqueRecoveryFraction R b a r₁ k₁ 0 (by simp)).value q +
        (complementaryRecoveryFraction R c a r₂ k₂).value q := by
  rw [obliqueRecoveryFraction_value,complementaryRecoveryFraction_value R c ha₀ ha₁]
  unfold twoChildRecovery
  dsimp only
  by_cases hq : coordinateRepresentative 1 (R.equiv q) < a
  · simp [hq,not_le_of_gt hq]
  · simp [hq,le_of_not_gt hq]

theorem phaseFraction_integrable (b : PhaseFraction) : Integrable b.value domainMeasure :=
  Integrable.of_bound b.measurable.aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun q => by simpa only [Real.norm_eq_abs] using phaseFraction_abs_le b q))

theorem twoChildRecovery_mean (R : TorusCoordinates) (b c : PhaseFraction)
    {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1) {r₁ k₁ r₂ k₂ : ℕ}
    (hr₁ : 0 < r₁) (hk₁ : 0 < k₁) (hr₂ : 0 < r₂) (hk₂ : 0 < k₂) :
    phaseMean (twoChildRecovery R b c a r₁ k₁ r₂ k₂) =
      a * phaseMean b + (1-a) * phaseMean c := by
  unfold phaseMean
  have heq := funext (twoChildRecovery_value_sum R b c ha₀ ha₁ r₁ k₁ r₂ k₂)
  rw [heq,integral_add (phaseFraction_integrable _) (phaseFraction_integrable _)]
  change phaseMean (obliqueRecoveryFraction R b a r₁ k₁ 0 (by simp)) +
    phaseMean (complementaryRecoveryFraction R c a r₂ k₂) = _
  rw [obliqueRecoveryFraction_mean R b ⟨ha₀,ha₁.le⟩ hr₁ hk₁,
    complementaryRecoveryFraction_mean R c ha₀ ha₁ hr₂ hk₂]
  simp only [phaseMean]
  ring

end HierarchicalLaminates.GClosure
