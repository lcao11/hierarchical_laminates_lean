module

public import HierarchicalLaminates.GClosure.GeneralLayerNormal
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Topology.Sequences

/-! Every real layer direction is a limit of periodic primitive integer directions. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open HierarchicalLaminates.Lamination Filter Set
open scoped Topology

def rationalCoordinates (q : ℚ) : TorusCoordinates :=
  coordinatesOfCoprime q.num (q.den : ℤ) (by simpa [Int.gcd_def] using q.reduced)

def negativeCoordinates (R : TorusCoordinates) : TorusCoordinates where
  matrix := -R.matrix
  inverse := -R.inverse
  inverse_mul := by simpa using R.inverse_mul
  mul_inverse := by simpa using R.mul_inverse

theorem coordinateNormal_negative (R : TorusCoordinates) :
    (coordinateNormal (negativeCoordinates R)).coordinates = -(coordinateNormal R).coordinates := by
  funext i
  simp [coordinateNormal,coordinateScale,negativeCoordinates]
  ring

def slopeCoordinates (t : ℝ) : Fin 2 → ℝ :=
  ![t / Real.sqrt (t^2+1), 1 / Real.sqrt (t^2+1)]

theorem slopeCoordinates_continuous : Continuous slopeCoordinates := by
  have hden : ∀ t : ℝ, Real.sqrt (t^2+1) ≠ 0 :=
    fun t => ne_of_gt (Real.sqrt_pos.2 (by positivity))
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_id.div ((continuous_id.pow 2).add continuous_const).sqrt hden
  · exact continuous_const.div ((continuous_id.pow 2).add continuous_const).sqrt hden

theorem coordinateScale_rational (q : ℚ) :
    coordinateScale (rationalCoordinates q) =
      (q.den : ℝ) * Real.sqrt ((q : ℝ)^2+1) := by
  have hd : (0 : ℝ) < q.den := by exact_mod_cast q.pos
  have hq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := Rat.cast_def q
  have heq : (q.num : ℝ)^2 + (q.den : ℝ)^2 =
      (q.den : ℝ)^2 * ((q : ℝ)^2+1) := by
    rw [hq]
    field_simp
  change Real.sqrt ((q.num : ℝ)^2 + (q.den : ℝ)^2) = _
  rw [heq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_pos hd]

theorem coordinateNormal_rational (q : ℚ) :
    (coordinateNormal (rationalCoordinates q)).coordinates = slopeCoordinates (q : ℝ) := by
  have hd : (0 : ℝ) < q.den := by exact_mod_cast q.pos
  have hs : 0 < Real.sqrt ((q : ℝ)^2+1) := Real.sqrt_pos.2 (by positivity)
  funext i
  fin_cases i
  · rw [coordinateNormal_apply,coordinateScale_rational]
    change (q.num : ℝ) / ((q.den : ℝ)*Real.sqrt ((q : ℝ)^2+1)) =
      (q : ℝ)/Real.sqrt ((q : ℝ)^2+1)
    rw [Rat.cast_def]
    field_simp
  · rw [coordinateNormal_apply,coordinateScale_rational]
    change (q.den : ℝ) / ((q.den : ℝ)*Real.sqrt ((q : ℝ)^2+1)) =
      1/Real.sqrt ((q : ℝ)^2+1)
    field_simp

theorem exists_rational_sequence (t : ℝ) :
    ∃ q : ℕ → ℚ, Tendsto (fun n => (q n : ℝ)) atTop (nhds t) := by
  have hmem : t ∈ closure (Set.range ((↑) : ℚ → ℝ)) := Rat.denseRange_cast t
  obtain ⟨v,hv,hlim⟩ := mem_closure_iff_seq_limit.mp hmem
  choose q hq using hv
  refine ⟨q,?_⟩
  simpa only [hq] using hlim

theorem slopeCoordinates_of_normal (n : LayerNormal) (hn : 0 < n.coordinates 1) :
    slopeCoordinates (n.coordinates 0 / n.coordinates 1) = n.coordinates := by
  have heq : (n.coordinates 0 / n.coordinates 1)^2+1 = (1 / n.coordinates 1)^2 := by
    field_simp
    nlinarith [n.unit_length]
  have hs : Real.sqrt ((n.coordinates 0 / n.coordinates 1)^2+1) = 1 / n.coordinates 1 := by
    rw [heq,Real.sqrt_sq_eq_abs,abs_of_pos (one_div_pos.mpr hn)]
  funext i
  fin_cases i
  · change (n.coordinates 0 / n.coordinates 1) /
      Real.sqrt ((n.coordinates 0 / n.coordinates 1)^2+1) = n.coordinates 0
    rw [hs]
    field_simp
  · change 1 / Real.sqrt ((n.coordinates 0 / n.coordinates 1)^2+1) = n.coordinates 1
    rw [hs]
    field_simp

theorem normalCoordinates_inducing : Topology.IsInducing LayerNormal.coordinates := ⟨rfl⟩

theorem normal_eq_of_coordinates {n m : LayerNormal}
    (h : n.coordinates = m.coordinates) : n = m := by
  cases n
  cases m
  cases h
  rfl

theorem exists_coordinateNormal_sequence_of_pos (n : LayerNormal) (hn : 0 < n.coordinates 1) :
    ∃ R : ℕ → TorusCoordinates,
      Tendsto (fun j => coordinateNormal (R j)) atTop (nhds n) := by
  obtain ⟨q,hq⟩ := exists_rational_sequence (n.coordinates 0 / n.coordinates 1)
  refine ⟨fun j => rationalCoordinates (q j),?_⟩
  apply normalCoordinates_inducing.tendsto_nhds_iff.mpr
  have h := slopeCoordinates_continuous.continuousAt.tendsto.comp hq
  simpa only [Function.comp_def,coordinateNormal_rational,slopeCoordinates_of_normal n hn] using h

def negativeNormal (n : LayerNormal) : LayerNormal where
  coordinates := -n.coordinates
  unit_length := by simpa using n.unit_length

theorem exists_coordinateNormal_sequence (n : LayerNormal) :
    ∃ R : ℕ → TorusCoordinates,
      Tendsto (fun j => coordinateNormal (R j)) atTop (nhds n) := by
  by_cases hp : 0 < n.coordinates 1
  · exact exists_coordinateNormal_sequence_of_pos n hp
  by_cases hz : n.coordinates 1 = 0
  · have hx : n.coordinates 0 = 1 ∨ n.coordinates 0 = -1 := by
      have heq : n.coordinates 0 ^ 2 = 1 := by nlinarith [n.unit_length]
      exact sq_eq_one_iff.mp heq
    let R := coordinatesOfCoprime 1 0 (by norm_num)
    have hR : (coordinateNormal R).coordinates = ![1,0] := by
      funext i
      fin_cases i <;>
        norm_num [coordinateNormal,coordinateScale,R,coordinatesOfCoprime,coordinatesOfBezout]
    rcases hx with hx | hx
    · refine ⟨fun _ => R,?_⟩
      have heq : coordinateNormal R = n := normal_eq_of_coordinates (by
        rw [hR]
        funext i
        fin_cases i <;> simp [hx,hz])
      change Tendsto (fun _ : ℕ => coordinateNormal R) atTop (nhds n)
      rw [heq]
      exact tendsto_const_nhds
    · refine ⟨fun _ => negativeCoordinates R,?_⟩
      have heq : coordinateNormal (negativeCoordinates R) = n := normal_eq_of_coordinates (by
        rw [coordinateNormal_negative,hR]
        funext i
        fin_cases i <;> simp [hx,hz])
      change Tendsto (fun _ : ℕ => coordinateNormal (negativeCoordinates R)) atTop (nhds n)
      rw [heq]
      exact tendsto_const_nhds
  · have hn : 0 < (negativeNormal n).coordinates 1 := by
      change 0 < -n.coordinates 1
      have hle := le_of_not_gt hp
      exact neg_pos.mpr (lt_of_le_of_ne hle hz)
    obtain ⟨R,hR⟩ := exists_coordinateNormal_sequence_of_pos (negativeNormal n) hn
    refine ⟨fun j => negativeCoordinates (R j),?_⟩
    apply normalCoordinates_inducing.tendsto_nhds_iff.mpr
    have h := normalCoordinates_continuous.continuousAt.tendsto.comp hR
    have hneg := h.neg
    simpa [Function.comp_def,coordinateNormal_negative,negativeNormal] using hneg

end HierarchicalLaminates.GClosure
