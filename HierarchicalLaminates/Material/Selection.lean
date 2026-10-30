module

public import HierarchicalLaminates.Material.Arrangements
public import HierarchicalLaminates.Corrector.Gap
public import HierarchicalLaminates.Binary.Mean
public import Mathlib.Topology.Algebra.Order.Field

/-!
# Selecting a finite even stripe count

A response-error estimate of order `1/N` and a positive limiting gap give
a sufficiently large even stripe count with positive energy difference.
-/

@[expose] public section
noncomputable section

namespace HierarchicalLaminates.Material

open MeasureTheory HierarchicalLaminates.Periodic HierarchicalLaminates.Lamination

theorem exists_positive_even_gap_of_bound {C : ℝ}
    (hbound : ∀ N : ℕ, 0 < N →
      |physicalLoadingDifference (binaryFraction N) -
        physicalLoadingDifference smoothFraction| ≤ C / (N : ℝ)) :
    ∃ M : ℕ, 0 < M ∧ 0 < physicalLoadingDifference (binaryFraction (M + M)) := by
  let d := physicalLoadingDifference smoothFraction
  have hd : 0 < d := Corrector.smooth_physical_loading_gap_positive
  obtain ⟨M, hM⟩ := exists_nat_gt (max 1 (C / d))
  have hMone : (1 : ℝ) < M := (le_max_left _ _).trans_lt hM
  have hMpos : 0 < M := by exact_mod_cast (lt_trans zero_lt_one hMone)
  have hMN : 0 < M + M := Nat.add_pos_left hMpos M
  have hNpos : (0 : ℝ) < ((M + M : ℕ) : ℝ) := by exact_mod_cast hMN
  have hCd : C < (M : ℝ) * d :=
    (div_lt_iff₀ hd).mp ((le_max_right _ _).trans_lt hM)
  have hsmall : C / ((M + M : ℕ) : ℝ) < d := by
    apply (div_lt_iff₀ hNpos).2
    push_cast
    nlinarith
  have he := (abs_le.mp (hbound (M + M) hMN)).1
  refine ⟨M, hMpos, ?_⟩
  change -(C / ((M + M : ℕ) : ℝ)) ≤
    physicalLoadingDifference (binaryFraction (M + M)) - d at he
  linarith

theorem exists_binary_separation_of_bound {C : ℝ}
    (hbound : ∀ N : ℕ, 0 < N →
      |physicalLoadingDifference (binaryFraction N) -
        physicalLoadingDifference smoothFraction| ≤ C / (N : ℝ)) :
    ∃ N : ℕ, 0 < N ∧ 2 ≤ N ∧
      (∫ q, Binary.binaryIndicator N q ∂domainMeasure) = 1 / 2 ∧
      0 < physicalLoadingDifference (binaryFraction N) ∧
      effectiveMatrix (binaryFraction N) ∉
        closure (allFiniteLaminates phaseZero (phaseOne rho)) := by
  obtain ⟨M, hM, hgap⟩ := exists_positive_even_gap_of_bound hbound
  exact ⟨M + M, Nat.add_pos_left hM M, by omega, Binary.binaryIndicator_mean_half_even hM,
    hgap, binary_positive_excludes_all_laminate_limits (M + M) hgap⟩

end HierarchicalLaminates.Material
