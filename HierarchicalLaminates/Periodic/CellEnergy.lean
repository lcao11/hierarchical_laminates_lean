module

public import HierarchicalLaminates.Periodic.WeakGradient
public import HierarchicalLaminates.Analysis.EffectiveTensor
public import HierarchicalLaminates.Analysis.VariationalClosure

/-!
# The closed-gradient solver represents the weak Sobolev cell energy

The admissible fields in `sobolevCellEnergy` are periodic weak gradients from
`WeakGradient`. Continuity of the quadratic energy identifies their infimum
with the minimum on the closed gradient space used by the cell solver for a
symmetric coercive coefficient law.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Periodic

open HierarchicalLaminates.Analysis

instance gradientSpace_complete : CompleteSpace gradientSpace :=
  weakGradientSpace.isClosed_topologicalClosure.completeSpace_coe

def fieldEnergy (A : PhysicalField →L[ℝ] PhysicalField) (F : PhysicalGradient)
    (g : PhysicalField) : ℝ :=
  inner ℝ (A (constantField F + g)) (constantField F + g)

theorem fieldEnergy_continuous (A : PhysicalField →L[ℝ] PhysicalField)
    (F : PhysicalGradient) : Continuous (fieldEnergy A F) :=
  (A.continuous.comp (continuous_const.add continuous_id)).inner
    (continuous_const.add continuous_id)

def weakCellEnergy (A : PhysicalField →L[ℝ] PhysicalField) (F : PhysicalGradient) : ℝ :=
  sInf (fieldEnergy A F '' (weakGradientSpace : Set PhysicalField))

def sobolevCellEnergy (A : PhysicalField →L[ℝ] PhysicalField) (F : PhysicalGradient) : ℝ :=
  sInf (Set.range fun u : SobolevPotential => fieldEnergy A F u.gradient)

theorem sobolevCellEnergy_eq_weakCellEnergy
    (A : PhysicalField →L[ℝ] PhysicalField) (F : PhysicalGradient) :
    sobolevCellEnergy A F = weakCellEnergy A F := by
  apply congrArg sInf
  ext r
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u.gradient, ⟨u.potential, u.weakGradient⟩, rfl⟩
  · rintro ⟨g, ⟨u, hu⟩, rfl⟩
    exact ⟨⟨u, g, hu⟩, rfl⟩

def periodicEffective (A : PhysicalField →L[ℝ] PhysicalField) (mu : ℝ)
    (hmu : 0 < mu) (hA : CoerciveLaw A mu) :
    PhysicalGradient →L[ℝ] PhysicalGradient :=
  effectiveOperator gradientSpace constantField meanField A mu hmu hA

theorem weakCellEnergy_eq_closedMinimum (A : PhysicalField →L[ℝ] PhysicalField)
    (hAs : SymmetricLaw A) (mu : ℝ) (hmu : 0 < mu) (hA : CoerciveLaw A mu)
    (F : PhysicalGradient) :
    weakCellEnergy A F =
      fieldEnergy A F (correction gradientSpace A mu hmu hA (constantField F)) := by
  let g0 : PhysicalField := correction gradientSpace A mu hmu hA (constantField F)
  have hg0 : g0 ∈ closure (weakGradientSpace : Set PhysicalField) :=
    (correction gradientSpace A mu hmu hA (constantField F)).property
  have hnonempty : (weakGradientSpace : Set PhysicalField).Nonempty :=
    ⟨0, weakGradientSpace.zero_mem⟩
  apply energy_sInf_eq_of_min_on_closure (fieldEnergy A F) (fieldEnergy_continuous A F)
    (weakGradientSpace : Set PhysicalField) hnonempty g0 hg0
  intro y hy
  have he := cellField_isCellField gradientSpace A mu hmu hA (constantField F)
  have hy' : y ∈ gradientSpace := by
    change y ∈ closure (weakGradientSpace : Set PhysicalField)
    exact hy
  have hadmissible : constantField F + y - constantField F ∈ gradientSpace := by
    simpa only [add_sub_cancel_left] using hy'
  have hmin := cell_energy_minimal hAs (le_of_lt hmu) hA he hadmissible
  exact hmin

/-- For a symmetric coercive law, the cell solver's energy equals the infimum
over periodic weak H¹ potentials. -/
theorem periodicEffective_energy (A : PhysicalField →L[ℝ] PhysicalField)
    (hAs : SymmetricLaw A) (mu : ℝ) (hmu : 0 < mu) (hA : CoerciveLaw A mu)
    (F : PhysicalGradient) :
    inner ℝ (periodicEffective A mu hmu hA F) F = sobolevCellEnergy A F := by
  rw [sobolevCellEnergy_eq_weakCellEnergy,
    weakCellEnergy_eq_closedMinimum A hAs mu hmu hA F]
  exact effectiveOperator_energy gradientSpace constantField meanField
    constant_mean_pairing A mu hmu hA F

theorem periodicEffective_symmetric (A : PhysicalField →L[ℝ] PhysicalField)
    (hAs : SymmetricLaw A) (mu : ℝ) (hmu : 0 < mu) (hA : CoerciveLaw A mu) :
    SymmetricLaw (periodicEffective A mu hmu hA) :=
  effectiveOperator_symmetric gradientSpace constantField meanField
    constant_mean_pairing A hAs mu hmu hA

theorem periodicCellField_mean (A : PhysicalField →L[ℝ] PhysicalField)
    (mu : ℝ) (hmu : 0 < mu) (hA : CoerciveLaw A mu) (F : PhysicalGradient) :
    meanField (cellField gradientSpace A mu hmu hA (constantField F)) = F := by
  have he := cellField_isCellField gradientSpace A mu hmu hA (constantField F)
  have hz := gradientSpace_mean_zero _ he.1
  rw [map_sub, mean_constantField] at hz
  exact sub_eq_zero.mp hz

/-- The mean-field lower bound uses the same ellipticity constant as the coefficient law. -/
theorem periodicEffective_coercive (A : PhysicalField →L[ℝ] PhysicalField)
    (mu : ℝ) (hmu : 0 < mu) (hA : CoerciveLaw A mu) :
    CoerciveLaw (periodicEffective A mu hmu hA) mu := by
  intro F
  let e := cellField gradientSpace A mu hmu hA (constantField F)
  have hn : ‖F‖ ≤ ‖e‖ := by
    rw [← periodicCellField_mean A mu hmu hA F]
    exact meanField_norm_le e
  have hco := hA e
  have hsq : ‖F‖ ^ 2 ≤ ‖e‖ ^ 2 := by
    nlinarith [norm_nonneg F, norm_nonneg e]
  have hm := mul_le_mul_of_nonneg_left hsq (le_of_lt hmu)
  have he := effectiveOperator_energy gradientSpace constantField meanField
    constant_mean_pairing A mu hmu hA F
  change inner ℝ (periodicEffective A mu hmu hA F) F = inner ℝ (A e) e at he
  rw [he]
  nlinarith

end HierarchicalLaminates.Periodic
