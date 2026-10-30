module

public import HierarchicalLaminates.Composition.Interfaces
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Order.Floor.Semiring

/-! Positive integral microscopic period counts with asymptotically equal scales. -/

@[expose] public section
noncomputable section

namespace HierarchicalLaminates.Composition

open Filter
open scoped Topology

def horizontalPeriods (n : ℕ) : ℕ := n + 1

def verticalPeriods (a : ℝ) (r : ℕ) : ℕ := ⌊a * (r : ℝ)⌋₊ + 1

theorem horizontalPeriods_pos (n : ℕ) : 0 < horizontalPeriods n := Nat.succ_pos n

theorem verticalPeriods_pos (a : ℝ) (r : ℕ) : 0 < verticalPeriods a r :=
  Nat.succ_pos _

theorem aspect_error_bound {a : ℝ} (ha : 0 < a) {r : ℕ} (hr : 0 < r) :
    |(verticalPeriods a r : ℝ) / (a * r) - 1| ≤ 1 / (a * r) := by
  have hden : 0 < a * (r : ℝ) := mul_pos ha (by exact_mod_cast hr)
  have hfloor := Nat.floor_le hden.le
  have hlt := Nat.lt_floor_add_one (a * (r : ℝ))
  have hk : (verticalPeriods a r : ℝ) = (⌊a * (r : ℝ)⌋₊ : ℝ) + 1 := by
    simp [verticalPeriods]
  rw [hk, abs_of_nonneg]
  · have heq : ((⌊a * (r : ℝ)⌋₊ : ℝ) + 1) / (a * r) - 1 =
        ((⌊a * (r : ℝ)⌋₊ : ℝ) + 1 - a * r) / (a * r) := by
      field_simp
    rw [heq]
    apply (div_le_div_iff_of_pos_right hden).2
    linarith
  · apply sub_nonneg.mpr
    apply (one_le_div hden).2
    exact hlt.le

theorem horizontalPeriods_inv_tendsto :
    Tendsto (fun n : ℕ => (horizontalPeriods n : ℝ)⁻¹) atTop (nhds 0) := by
  simpa [horizontalPeriods, one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem aspect_error_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ =>
      |(verticalPeriods a (horizontalPeriods n) : ℝ) / (a * horizontalPeriods n) - 1|)
      atTop (nhds 0) := by
  have hupper : Tendsto (fun n : ℕ => 1 / (a * (horizontalPeriods n : ℝ)))
      atTop (nhds 0) := by
    simpa [one_div, mul_inv_rev, mul_comm] using horizontalPeriods_inv_tendsto.mul_const a⁻¹
  exact squeeze_zero (fun _ => abs_nonneg _)
    (fun n => aspect_error_bound ha (horizontalPeriods_pos n)) hupper

theorem exists_small_width {a ε : ℝ} (ha : 0 < a) (M : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ 4 * δ < a ∧ M * Real.sqrt (4 * δ) < ε := by
  have hδ := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hband : Tendsto (fun n : ℕ => M * Real.sqrt (4 * (1 / ((n : ℝ) + 1))))
      atTop (nhds 0) := by
    simpa using (Real.continuous_sqrt.continuousAt.tendsto.comp
      (hδ.const_mul 4)).const_mul M
  have hδ4 : Tendsto (fun n : ℕ => 4 * (1 / ((n : ℝ) + 1))) atTop (nhds 0) := by
    simpa using hδ.const_mul 4
  have hsmall : ∀ᶠ n : ℕ in atTop, 4 * (1 / ((n : ℝ) + 1)) < a :=
    hδ4.eventually (gt_mem_nhds ha)
  obtain ⟨n, hn, hb⟩ := (hsmall.and (hband.eventually (gt_mem_nhds hε))).exists
  exact ⟨1 / ((n : ℝ) + 1), by positivity, hn, hb⟩

theorem exists_micro_scale {a ε : ℝ} (ha : 0 < a) (M D : ℝ) (hε : 0 < ε) :
    ∃ r k : ℕ, 0 < r ∧ 0 < k ∧
      M * |(k : ℝ) / (a * r) - 1| + (r : ℝ)⁻¹ * D < ε := by
  have hlim : Tendsto (fun n : ℕ =>
      M * |(verticalPeriods a (horizontalPeriods n) : ℝ) /
        (a * horizontalPeriods n) - 1| + (horizontalPeriods n : ℝ)⁻¹ * D)
      atTop (nhds 0) := by
    simpa using ((aspect_error_tendsto ha).const_mul M).add
      (horizontalPeriods_inv_tendsto.mul_const D)
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  exact ⟨horizontalPeriods n, verticalPeriods a (horizontalPeriods n),
    horizontalPeriods_pos n, verticalPeriods_pos _ _, hn⟩

end HierarchicalLaminates.Composition
