module

public import HierarchicalLaminates.Binary.Primitive
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Classical stripe-primitive derivatives away from its moving interface. -/

@[expose] public section

namespace HierarchicalLaminates.Binary

open Filter Topology

noncomputable def stripeIndicator (tau t : ℝ) : ℝ := if tau < t then 1 else 0

theorem primitive_derivative_left (h tau t : ℝ) (hlt : tau < t) :
    HasDerivAt (fun q => stripePrimitive h q t) (h * (1 - t)) tau := by
  have heq : (fun q => stripePrimitive h q t) =ᶠ[𝓝 tau]
      (fun q => h * (q - q * t)) :=
    Filter.Eventually.mono (p := fun q : ℝ => q < t) (Iio_mem_nhds hlt) fun q hq => by
      simp only [stripePrimitive, min_eq_left (le_of_lt hq)]
  have hd := ((hasDerivAt_id tau).sub ((hasDerivAt_id tau).mul_const t)).const_mul h
  have hd' : HasDerivAt (fun q => h * (q - q * t)) (h * (1 - t)) tau := by
    simpa using hd
  exact hd'.congr_of_eventuallyEq heq

theorem primitive_derivative_right (h tau t : ℝ) (hlt : t < tau) :
    HasDerivAt (fun q => stripePrimitive h q t) (h * (-t)) tau := by
  have heq : (fun q => stripePrimitive h q t) =ᶠ[𝓝 tau]
      (fun q => h * (t - q * t)) :=
    Filter.Eventually.mono (p := fun q : ℝ => t < q) (Ioi_mem_nhds hlt) fun q hq => by
      simp only [stripePrimitive, min_eq_right (le_of_lt hq)]
  have hd := ((hasDerivAt_const tau t).sub ((hasDerivAt_id tau).mul_const t)).const_mul h
  have hd' : HasDerivAt (fun q => h * (t - q * t)) (h * (-t)) tau := by
    simpa using hd
  exact hd'.congr_of_eventuallyEq heq

theorem primitive_derivative (h tau t : ℝ) (hne : tau ≠ t) :
    HasDerivAt (fun q => stripePrimitive h q t)
      (h * (stripeIndicator tau t - t)) tau := by
  by_cases hlt : tau < t
  · simpa only [stripeIndicator, ite_eq_left hlt] using primitive_derivative_left h tau t hlt
  · have hgt : t < tau := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)
    simpa only [stripeIndicator, ite_eq_right hlt, zero_sub] using
      primitive_derivative_right h tau t hgt

theorem primitive_swap (h tau t : ℝ) :
    stripePrimitive h tau t = stripePrimitive h t tau := by
  unfold stripePrimitive
  rw [min_comm tau t, mul_comm tau t]

theorem primitive_width_derivative (h tau t : ℝ) (hne : t ≠ tau) :
    HasDerivAt (fun s => stripePrimitive h tau s)
      (h * (stripeIndicator t tau - tau)) t := by
  have hd := primitive_derivative h t tau hne
  apply hd.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun s => primitive_swap h tau s)

theorem primitive_derivative_bound {h tau t : ℝ} (hh : 0 ≤ h)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |h * (stripeIndicator tau t - t)| ≤ h := by
  unfold stripeIndicator
  split_ifs
  · rw [abs_of_nonneg (mul_nonneg hh (sub_nonneg.mpr ht.2))]
    nlinarith [mul_nonneg hh ht.1]
  · rw [zero_sub, mul_neg, abs_neg, abs_of_nonneg (mul_nonneg hh ht.1)]
    nlinarith [mul_nonneg hh (sub_nonneg.mpr ht.2)]

end HierarchicalLaminates.Binary
