module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Exact scalar parameters

The rational constants `kappa` and `rho` set the fifth-order coefficient and
the chosen contrast. The scalar estimates give a positive loading difference
from an explicit remainder bound.
-/

@[expose] public section

namespace HierarchicalLaminates

def kappaQ : ℚ := 1 / 1062744883200

def rhoQ : ℚ := kappaQ / 32

theorem kappaQ_pos : 0 < kappaQ := by decide +kernel

theorem rhoQ_pos : 0 < rhoQ := by decide +kernel

theorem rhoQ_lt_one_third : rhoQ < 1 / 3 := by decide +kernel

theorem rhoQ_value : rhoQ = 1 / 34007836262400 := by decide +kernel

theorem kappaQ_gt_two_neg40 : 1 / (2 : ℚ) ^ 40 < kappaQ := by decide +kernel

theorem rhoQ_gt_two_neg45 : 1 / (2 : ℚ) ^ 45 < rhoQ := by decide +kernel

noncomputable section

def kappa : ℝ := (kappaQ : ℝ)

def rho : ℝ := (rhoQ : ℝ)

theorem kappa_pos : 0 < kappa := by
  norm_num [kappa, kappaQ]

theorem rho_pos : 0 < rho := by
  norm_num [rho, rhoQ, kappaQ]

theorem rho_lt_one_third : rho < 1 / 3 := by
  norm_num [rho, rhoQ, kappaQ]

theorem rho_lt_two_thirds : rho < 2 / 3 := by
  linarith [rho_lt_one_third]

theorem rho_eq_kappa_div : rho = kappa / 32 := by
  norm_num [rho, rhoQ, kappa, kappaQ]

theorem rho_value : rho = 1 / 34007836262400 := by
  norm_num [rho, rhoQ, kappaQ]

theorem kappa_gt_two_neg40 : 1 / (2 : ℝ) ^ 40 < kappa := by
  norm_num [kappa, kappaQ]

theorem rho_gt_two_neg45 : 1 / (2 : ℝ) ^ 45 < rho := by
  norm_num [rho, rhoQ, kappaQ]

theorem contraction_pos : 0 < 1 - 3 * rho / 2 := by
  linarith [rho_lt_one_third]

theorem contraction_lt_one : 3 * rho / 2 < 1 := by
  linarith [rho_lt_one_third]

theorem analytic_tail_le :
    (3 / 2 : ℝ) ^ 5 * rho ^ 6 / (1 - 3 * rho / 2) ≤
      (243 / 16 : ℝ) * rho ^ 6 := by
  have hden : (1 / 2 : ℝ) ≤ 1 - 3 * rho / 2 := by
    linarith [rho_lt_one_third]
  apply (div_le_iff₀ contraction_pos).2
  have hmul := mul_le_mul_of_nonneg_left hden
    (show 0 ≤ (243 / 16 : ℝ) * rho ^ 6 by positivity)
  norm_num at hmul ⊢
  nlinarith [hmul]

theorem tail_upper_eq :
    (243 / 16 : ℝ) * rho ^ 6 = (243 / 512 : ℝ) * kappa * rho ^ 5 := by
  rw [rho_eq_kappa_div]
  ring

theorem tail_upper_lt_half :
    (243 / 16 : ℝ) * rho ^ 6 < (1 / 2 : ℝ) * kappa * rho ^ 5 := by
  rw [tail_upper_eq]
  have hpos : 0 < kappa * rho ^ 5 := mul_pos kappa_pos (pow_pos rho_pos _)
  nlinarith

theorem delta_tail_upper_eq :
    2 * ((243 / 16 : ℝ) * rho ^ 6) =
      (243 / 256 : ℝ) * kappa * rho ^ 5 := by
  rw [tail_upper_eq]
  ring

theorem smooth_gap_lower_eq :
    2 * kappa * rho ^ 5 - 2 * ((243 / 16 : ℝ) * rho ^ 6) =
      (269 / 256 : ℝ) * kappa * rho ^ 5 := by
  rw [delta_tail_upper_eq]
  ring

/-- The scalar lower bound obtained from an effective-response error estimate. -/
theorem smooth_gap_lower {delta : ℝ}
    (herror : |delta - 2 * kappa * rho ^ 5| ≤
      (243 / 256 : ℝ) * kappa * rho ^ 5) :
    (269 / 256 : ℝ) * kappa * rho ^ 5 ≤ delta := by
  have hneg := neg_le_of_abs_le herror
  linarith

theorem smooth_gap_positive {delta : ℝ}
    (herror : |delta - 2 * kappa * rho ^ 5| ≤
      (243 / 256 : ℝ) * kappa * rho ^ 5) : 0 < delta := by
  have hpos : 0 < (269 / 256 : ℝ) * kappa * rho ^ 5 := by
    exact mul_pos (mul_pos (by norm_num) kappa_pos) (pow_pos rho_pos _)
  exact lt_of_lt_of_le hpos (smooth_gap_lower herror)

end

end HierarchicalLaminates
