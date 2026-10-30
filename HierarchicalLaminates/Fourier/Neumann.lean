module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# A norm-convergent Neumann construction

For a contracting bounded linear map on a real Banach space, the geometric
series converges to a solution of the fixed-point equation with an explicit
remainder bound.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Fourier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def neumannTerm (A : E →L[ℝ] E) (f : E) : ℕ → E
  | 0 => f
  | n + 1 => A (neumannTerm A f n)

@[simp]
theorem neumannTerm_zero (A : E →L[ℝ] E) (f : E) : neumannTerm A f 0 = f := rfl

@[simp]
theorem neumannTerm_succ (A : E →L[ℝ] E) (f : E) (n : ℕ) :
    neumannTerm A f (n + 1) = A (neumannTerm A f n) := rfl

theorem neumannTerm_norm_le (A : E →L[ℝ] E) {q : ℝ} (hq : 0 ≤ q)
    (hA : ∀ v, ‖A v‖ ≤ q * ‖v‖) (f : E) (n : ℕ) :
    ‖neumannTerm A f n‖ ≤ ‖f‖ * q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        ‖neumannTerm A f (n + 1)‖ ≤ q * ‖neumannTerm A f n‖ := hA _
        _ ≤ q * (‖f‖ * q ^ n) := mul_le_mul_of_nonneg_left ih hq
        _ = ‖f‖ * q ^ (n + 1) := by rw [pow_succ]; ring

variable [CompleteSpace E]

theorem neumannTerm_summable (A : E →L[ℝ] E) {q : ℝ} (hq : 0 ≤ q)
    (hqlt : q < 1) (hA : ∀ v, ‖A v‖ ≤ q * ‖v‖) (f : E) :
    Summable (neumannTerm A f) := by
  have hgeom : Summable (fun n : ℕ => ‖f‖ * q ^ n) :=
    (summable_geometric_of_lt_one hq hqlt).mul_left ‖f‖
  exact hgeom.of_norm_bounded (neumannTerm_norm_le A hq hA f)

def neumannSolution (A : E →L[ℝ] E) (f : E) : E := ∑' n, neumannTerm A f n

theorem neumannSolution_equation (A : E →L[ℝ] E) {q : ℝ} (hq : 0 ≤ q)
    (hqlt : q < 1) (hA : ∀ v, ‖A v‖ ≤ q * ‖v‖) (f : E) :
    neumannSolution A f = f + A (neumannSolution A f) := by
  have hs := neumannTerm_summable A hq hqlt hA f
  unfold neumannSolution
  rw [A.map_tsum hs]
  simpa only [neumannTerm_zero, neumannTerm_succ] using hs.tsum_eq_zero_add

theorem neumannSolution_tail (A : E →L[ℝ] E) {q : ℝ} (hq : 0 ≤ q)
    (hqlt : q < 1) (hA : ∀ v, ‖A v‖ ≤ q * ‖v‖) (f : E) (N : ℕ) :
    ‖neumannSolution A f - ∑ n ∈ Finset.range N, neumannTerm A f n‖ ≤
      ‖f‖ * q ^ N / (1 - q) := by
  rw [norm_sub_rev]
  exact norm_sub_le_of_geometric_bound_of_hasSum hqlt
    (neumannTerm_norm_le A hq hA f)
    (neumannTerm_summable A hq hqlt hA f).hasSum N

omit [CompleteSpace E] in
theorem neumannSolution_unique (A : E →L[ℝ] E) {q : ℝ} (hqlt : q < 1)
    (hA : ∀ v, ‖A v‖ ≤ q * ‖v‖) {f x y : E}
    (hx : x = f + A x) (hy : y = f + A y) : x = y := by
  have hsub : x - y = A (x - y) := by
    calc
      x - y = (f + A x) - (f + A y) := congrArg₂ (fun u v : E => u - v) hx hy
      _ = A x - A y := by abel
      _ = A (x - y) := (map_sub A x y).symm
  have hnorm := hA (x - y)
  rw [← hsub] at hnorm
  have hz : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

end HierarchicalLaminates.Fourier
