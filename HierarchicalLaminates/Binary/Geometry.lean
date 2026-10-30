module

public import HierarchicalLaminates.Binary.PrimitiveCalculus
public import HierarchicalLaminates.Fourier.CosineProfile
public import HierarchicalLaminates.Periodic.FieldSpace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Positivity

/-!
# Sampled-width binary geometry

Coordinates are represented in `[0,1)`. In each strip, the zero-one indicator
uses the width given by the sampled cosine phase-fraction profile.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Binary

open MeasureTheory HierarchicalLaminates.Periodic HierarchicalLaminates.Fourier

def coordinateRepresentative (i : Fin 2) (q : Domain) : ℝ :=
  (AddCircle.equivIco 1 0 (q i)).1

theorem coordinateRepresentative_mem (i : Fin 2) (q : Domain) :
    coordinateRepresentative i q ∈ Set.Ico (0 : ℝ) 1 := by
  simpa only [coordinateRepresentative, zero_add] using (AddCircle.equivIco 1 0 (q i)).2

theorem coordinateRepresentative_measurable (i : Fin 2) :
    Measurable (coordinateRepresentative i) := by
  exact measurable_subtype_coe.comp
    ((AddCircle.measurableEquivIco 1 0).measurable.comp (measurable_pi_apply i))

def stripIndex (N : ℕ) (q : Domain) : ℤ :=
  ⌊(N : ℝ) * coordinateRepresentative 1 q⌋

def stripCoordinate (N : ℕ) (q : Domain) : ℝ :=
  (N : ℝ) * coordinateRepresentative 1 q - (stripIndex N q : ℝ)

def sampledPoint (N : ℕ) (q : Domain) : Domain :=
  ![q 0, (((stripIndex N q : ℝ) / N : ℝ) : UnitAddCircle)]

def sampledFraction (N : ℕ) (q : Domain) : ℝ :=
  cosineProfile (sampledPoint N q)

def binaryIndicator (N : ℕ) (q : Domain) : ℝ :=
  stripeIndicator (stripCoordinate N q) (sampledFraction N q)

def binaryPrimitive (N : ℕ) (q : Domain) : ℝ :=
  stripePrimitive (1 / (N : ℝ)) (stripCoordinate N q) (sampledFraction N q)

theorem stripCoordinate_mem (N : ℕ) (q : Domain) :
    stripCoordinate N q ∈ Set.Ico (0 : ℝ) 1 := by
  constructor
  · exact sub_nonneg.mpr (Int.floor_le _)
  · have h := Int.lt_floor_add_one ((N : ℝ) * coordinateRepresentative 1 q)
    change (N : ℝ) * coordinateRepresentative 1 q -
      (⌊(N : ℝ) * coordinateRepresentative 1 q⌋ : ℝ) < 1
    linarith

theorem stripIndex_measurable (N : ℕ) : Measurable (stripIndex N) :=
  (measurable_const.mul (coordinateRepresentative_measurable 1)).floor

theorem stripIndex_real_measurable (N : ℕ) :
    Measurable (fun q => (stripIndex N q : ℝ)) :=
  (measurable_of_countable (fun k : ℤ => (k : ℝ))).comp (stripIndex_measurable N)

theorem stripCoordinate_measurable (N : ℕ) : Measurable (stripCoordinate N) :=
  (measurable_const.mul (coordinateRepresentative_measurable 1)).sub
    (stripIndex_real_measurable N)

theorem sampledPoint_measurable (N : ℕ) : Measurable (sampledPoint N) := by
  apply Measurable.of_eval
  intro i
  fin_cases i
  · exact measurable_pi_apply 0
  · have hm : Measurable (fun r : ℝ => (r : UnitAddCircle)) :=
      AddCircle.measurable_mk'
    exact hm.comp ((stripIndex_real_measurable N).div_const (N : ℝ))

theorem sampledFraction_measurable (N : ℕ) : Measurable (sampledFraction N) :=
  cosineProfile.continuous.measurable.comp (sampledPoint_measurable N)

theorem binaryIndicator_measurable (N : ℕ) : Measurable (binaryIndicator N) := by
  exact Measurable.ite
    (measurableSet_lt (stripCoordinate_measurable N) (sampledFraction_measurable N))
    measurable_const measurable_const

theorem binaryPrimitive_measurable (N : ℕ) : Measurable (binaryPrimitive N) := by
  exact measurable_const.mul
    (((stripCoordinate_measurable N).min (sampledFraction_measurable N)).sub
      ((stripCoordinate_measurable N).mul (sampledFraction_measurable N)))

theorem sampledFraction_mem (N : ℕ) (q : Domain) :
    sampledFraction N q ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨cosineProfile_nonneg _, cosineProfile_le_one _⟩

theorem binaryIndicator_values (N : ℕ) (q : Domain) :
    binaryIndicator N q = 0 ∨ binaryIndicator N q = 1 := by
  unfold binaryIndicator stripeIndicator
  split_ifs <;> simp

theorem binaryIndicator_mem (N : ℕ) (q : Domain) :
    binaryIndicator N q ∈ Set.Icc (0 : ℝ) 1 := by
  rcases binaryIndicator_values N q with h | h <;> simp [h]

theorem binaryPrimitive_bounds {N : ℕ} (hN : 0 < N) (q : Domain) :
    0 ≤ binaryPrimitive N q ∧ binaryPrimitive N q ≤ 1 / (4 * (N : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have htau := stripCoordinate_mem N q
  have h := primitive_bounds (le_of_lt (one_div_pos.mpr hNr))
    (show stripCoordinate N q ∈ Set.Icc (0 : ℝ) 1 from ⟨htau.1, le_of_lt htau.2⟩)
    (sampledFraction_mem N q)
  change 0 ≤ _ ∧ _ ≤ _
  constructor
  · exact h.1
  · exact h.2.trans_eq (by ring)

end HierarchicalLaminates.Binary
