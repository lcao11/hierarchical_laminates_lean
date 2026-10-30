module

public import HierarchicalLaminates.Binary.Mean
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Exact half fraction for every stripe count

The finite-mean formula for the sampled binary profile contains a discrete
Fourier sum. Expressing the samples as powers of a primitive root of unity
makes this sum vanish for every stripe count `N ≥ 2`, including odd counts.
The resulting binary indicator has normalized mean exactly one half.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.Binary

open MeasureTheory Periodic

/-- Equally spaced first Fourier samples are powers of one exponential. -/
theorem fourier_sample_power (N k : ℕ) :
    fourier 1 ((((k : ℝ) / N : ℝ)) : UnitAddCircle) =
      (Complex.exp (2 * Real.pi * Complex.I / N)) ^ k := by
  rw [fourier_coe_apply]
  simp only [Int.cast_one, mul_one, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.ofReal_one, div_one]
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

/-- The real parts of the first Fourier samples sum to zero over a full
period with at least two samples. -/
theorem fourier_sample_sum {N : ℕ} (hN : 2 ≤ N) :
    (∑ k ∈ Finset.range N,
      (fourier 1 ((((k : ℝ) / N : ℝ)) : UnitAddCircle)).re) = 0 := by
  have hsum : (∑ k ∈ Finset.range N,
      fourier 1 ((((k : ℝ) / N : ℝ)) : UnitAddCircle)) = 0 := by
    simp_rw [fourier_sample_power]
    exact (Complex.isPrimitiveRoot_exp N (by omega)).geom_sum_eq_zero (by omega)
  simpa using congrArg Complex.re hsum

/-- Every sampled binary profile with at least two stripes has exact half fraction. -/
theorem binaryIndicator_mean_half {N : ℕ} (hN : 2 ≤ N) :
    (∫ q, binaryIndicator N q ∂domainMeasure) = (1 / 2 : ℝ) := by
  have hpos : 0 < N := by omega
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hpos)
  rw [binaryIndicator_mean_finite hpos]
  simp_rw [add_div, mul_div_assoc]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← Finset.sum_div, fourier_sample_sum hN]
  field_simp
  ring

end HierarchicalLaminates.Binary
