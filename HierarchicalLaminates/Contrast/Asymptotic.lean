module

public import HierarchicalLaminates.Contrast.CellIdentification
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# Fifth-order expansion of the physical energy gap

For `0 ≤ r < 2 / 3`, the selected physical cell-energy difference has leading
term `2 * kappa * r ^ 5` and an explicit sixth-order remainder. The bound
`32 * r ^ 6` is uniform on `0 ≤ r < 1 / 3`, yielding a right-neighborhood
big-O expansion and strict positivity for sufficiently small positive `r`.

Specialization to `rho` recovers the construction's fixed-contrast energy
difference and its sharper numerical lower bound.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.Contrast

open Filter Topology Asymptotics Lamination

theorem physicalGap_error {r : ℝ} (hr : 0 ≤ r) (hrlt : r < 2/3) :
    |physicalGap r-2*kappa*r^5| ≤ 2*(3/2 : ℝ)^5*r^6/(1-3*r/2) := by
  rw [physicalGap_eq_sequence hr hrlt]
  exact sequenceLoading_error hr hrlt

/-- The physical remainder is bounded by `32 * r ^ 6` on `0 ≤ r < 1 / 3`. -/
theorem physicalGap_error_uniform {r : ℝ} (hr : 0 ≤ r) (hrlt : r < 1/3) :
    |physicalGap r-2*kappa*r^5| ≤ 32*r^6 := by
  rw [physicalGap_eq_sequence hr (by linarith : r < 2/3)]
  exact sequenceLoading_error_uniform hr hrlt

/-- The physical energy gap is `2 * kappa * r ^ 5 + O(r ^ 6)` as `r → 0⁺`. -/
theorem physicalGap_asymptotic :
    (fun r : ℝ => physicalGap r-2*kappa*r^5) =O[𝓝[>] (0 : ℝ)] (fun r : ℝ => r^6) := by
  apply Asymptotics.IsBigO.of_bound 32
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),0 < r := self_mem_nhdsWithin
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),r < 1/3 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1/3 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos,hsmall] with r hr hs
  simpa only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hr.le 6)] using
    physicalGap_error_uniform hr.le hs

theorem physicalGap_positive_of_small {r : ℝ} (hr : 0 < r) (hrlt : r < 1/3)
    (hsmall : r ≤ kappa/32) : 0 < physicalGap r := by
  have he := (abs_le.mp (physicalGap_error_uniform hr.le hrlt)).1
  have hp : 0 < kappa*r^5 := mul_pos kappa_pos (pow_pos hr 5)
  have hmul : 32*r^6 ≤ kappa*r^5 := by
    have h := mul_le_mul_of_nonneg_right (show 32*r ≤ kappa by linarith)
      (pow_nonneg hr.le 5)
    convert h using 1; ring
  linarith

/-- The selected physical cell-energy gap is positive for all sufficiently small `r > 0`. -/
theorem physicalGap_eventually_positive :
    ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),0 < physicalGap r := by
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),0 < r := self_mem_nhdsWithin
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),r < min (1/3 : ℝ) (kappa/32) :=
    (eventually_lt_nhds (lt_min (by norm_num) (div_pos kappa_pos (by norm_num) : (0 : ℝ) < kappa/32))).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [hpos,hsmall] with r hr hs
  exact physicalGap_positive_of_small hr (lt_min_iff.mp hs).1 (lt_min_iff.mp hs).2.le

theorem physicalGap_rho : physicalGap rho = Material.physicalLoadingDifference Material.smoothFraction := by
  simp only [physicalGap,coefficientLaw_rho]
  rw [← Material.effectiveMatrix_quadratic_energy Material.smoothFraction (WithLp.toLp 2 etaFlat),
    ← Material.effectiveMatrix_quadratic_energy Material.smoothFraction (WithLp.toLp 2 xiFlat)]
  rfl

/-- At `rho`, the physical gap satisfies the bound `(269 / 256) * kappa * rho ^ 5`. -/
theorem physicalGap_rho_lower : (269/256 : ℝ)*kappa*rho^5 ≤ physicalGap rho := by
  rw [physicalGap_rho,Corrector.smooth_physical_loading_gap_eq_sequence]
  exact reduced_solution_gap_lower

end HierarchicalLaminates.Contrast
